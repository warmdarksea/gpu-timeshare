# services.gpu-timeshare: one GPU, many models, the OpenAI API in front.
#
# Every model runs as its own systemd unit, gpu-timeshare-model-NAME,
# which nothing starts but gpu-timeshare -- and gpu-timeshare can do no more
# than start and stop exactly those units (a polkit rule), so what runs,
# and how it is sandboxed, is fixed here, not by the service:
#
#   - a throwaway user per run (DynamicUser), the file system read-only
#     but for its own cache, no home, no access to gpu-timeshare's state;
#   - the GPU's device nodes and nothing else (DevicePolicy=closed);
#   - a network namespace of its own (PrivateNetwork): a loopback no one
#     else shares and nothing beyond it. It answers on a unix socket only
#     gpu-timeshare can connect to -- its own `{socket}`, or, for a server
#     that only does TCP, `{port}` on its private loopback with
#     systemd-socket-proxyd (inside the same namespace) relaying that
#     socket to it;
#   - no capabilities, no new privileges, the @system-service syscalls;
#   - stopped as a cgroup: every process it forked goes with it, so a
#     stopped model never leaves VRAM behind.
#
#   services.gpu-timeshare = {
#     enable = true;
#     host = "0.0.0.0";               # TLS turns on by itself off loopback
#     openFirewall = true;
#     models.qwen = {
#       command = [ "${vllm}/bin/vllm" "serve" "${weights}" "--uds" "{socket}" ... ];
#       cost = 0.95;
#       concurrency = 8;
#     };
#   };
#
# Clients, as the service user:
#   sudo -u gpu-timeshare gpu-timeshare-admin token add alice   # prints alice's token, once
# and then any OpenAI client, with base_url https://HOST:8100/v1 and that
# token as its API key, trusting /var/lib/gpu-timeshare/tls/timeshare.crt
# (self-signed, made on the first start, unless tls.certFile is set).
{ config, lib, pkgs, utils, ... }:
let
  cfg = config.services.gpu-timeshare;
  inherit (lib) mkOption types;

  stateDir = "/var/lib/gpu-timeshare";
  socketDir = "/run/gpu-timeshare-models";
  socketGroup = "gpu-timeshare-models";
  loopback = builtins.elem cfg.host [ "127.0.0.1" "::1" "localhost" ];
  selfSigned = cfg.tls.enable && cfg.tls.certFile == null;
  tlsDir = "${stateDir}/tls";
  certFile = if selfSigned then "${tlsDir}/timeshare.crt" else cfg.tls.certFile;
  keyFile = if selfSigned then "${tlsDir}/timeshare.key" else cfg.tls.keyFile;

  unitName = name: "gpu-timeshare-model-${lib.replaceStrings [ "/" ":" ] [ "-" "-" ] name}";
  socketOf = name: "${socketDir}/${lib.replaceStrings [ "/" ":" ] [ "-" "-" ] name}.sock";
  units = lib.filterAttrs (_: m: m.isolation == "unit") cfg.models;

  # a unit model on {port} listens here, on its own loopback, and a proxy
  # in its namespace relays its socket to it
  privatePort = 8000;
  usesPort = m: lib.any (lib.hasInfix "{port}") m.command;
  proxied = lib.filterAttrs (_: usesPort) units;
  proxyName = name: "${unitName name}-proxy";

  # the GPU, as cgroup device rules: the nvidia nodes by their driver's
  # names in /proc/devices, so every card and the uvm/caps nodes match
  gpuDevices = [
    "char-nvidia-frontend rw" # /dev/nvidia0.., nvidiactl, nvidia-modeset
    "char-nvidia-uvm rw" # /dev/nvidia-uvm, nvidia-uvm-tools
    "char-nvidia-caps rw" # /dev/nvidia-caps/*
  ];

  modelOptions = { name, ... }: {
    options = {
      command = mkOption {
        type = types.listOf types.str;
        example = lib.literalExpression ''[ "''${vllm-env}/bin/vllm" "serve" "''${weights}" "--uds" "{socket}" ]'';
        description = ''
          The server, as argv. It must speak the OpenAI HTTP API. `{socket}`
          is replaced by the unix socket it should listen on, `{port}` by
          a TCP port on 127.0.0.1. In a unit, that loopback is its own
          (gpu-timeshare reaches it through a proxy in its namespace), so
          prefer `{port}` to a server's unix socket only for a server
          that has none. With isolation = "process", `{port}` is on the
          host's loopback, where any local user can reach it.
        '';
      };
      url = mkOption {
        type = types.nullOr types.str;
        default = null;
        description = "Where it answers, when not on `{socket}` (http://127.0.0.1:PORT or unix:/path).";
      };
      cost = mkOption {
        type = types.numbers.between 0 1000;
        default = 1;
        description = "Its share of `capacity` (for vllm: its --gpu-memory-utilization).";
      };
      concurrency = mkOption {
        type = types.ints.positive;
        default = 4;
        description = "Requests in flight to it at once (for vllm: its --max-num-seqs).";
      };
      ready = mkOption {
        type = types.str;
        default = "/v1/models";
        description = "A path that answers 200 once it can take requests.";
      };
      upstreamModel = mkOption {
        type = types.nullOr types.str;
        default = null;
        description = "The model name it expects; default: the first one its /v1/models lists.";
      };
      fingerprint = mkOption {
        type = types.nullOr types.str;
        default = null;
        description = ''
          What identifies its answers: part of the cache key, and returned
          as system_fingerprint. Default: derived from `command`, which on
          nix names the weights' store path.
        '';
      };
      startTimeout = mkOption {
        type = types.nullOr types.str;
        default = null;
        example = "20m";
        description = "How long it may take to load; default: scheduler.start_timeout.";
      };
      cache = mkOption {
        type = types.nullOr types.bool;
        default = null;
        description = "Cache its answers; default: cache.enabled.";
      };
      environment = mkOption {
        type = types.attrsOf types.str;
        default = { };
        description = "Its environment.";
      };
      isolation = mkOption {
        type = types.enum [ "unit" "process" ];
        default = "unit";
        description = ''
          "unit": its own sandboxed systemd unit (see the top of this
          module). "process": a child of gpu-timeshare, inside the
          service's own (looser) sandbox -- for a server that can't live in
          the strict one.
        '';
      };
      gpu = mkOption {
        type = types.bool;
        default = true;
        description = "Give its unit the nvidia device nodes; false leaves it no devices at all.";
      };
      network = mkOption {
        type = types.bool;
        default = false;
        description = ''
          Give its unit the host's network instead of a namespace of its
          own (a model that proxies a hosted API). It must then listen on
          `{socket}`.
        '';
      };
      serviceConfig = mkOption {
        type = types.attrsOf types.anything;
        default = { };
        example = { MemoryMax = "48G"; };
        description = "Merged into its unit's serviceConfig: resource limits, or loosening the sandbox.";
      };
    };
  };

  toml = pkgs.formats.toml { };

  modelSettings = name: m:
    lib.filterAttrs (_: v: v != null) {
      cost = m.cost;
      concurrency = m.concurrency;
      ready = m.ready;
      upstream_model = m.upstreamModel;
      fingerprint = m.fingerprint;
      start_timeout = m.startTimeout;
      cache = m.cache;
    }
    // (if m.isolation == "unit" then {
      unit = "${unitName name}.service";
      url = if m.url != null then m.url else "unix:${socketOf name}";
      # the command is the unit's; it still identifies the answers
      fingerprint = if m.fingerprint != null then m.fingerprint
        else "unit:" + builtins.hashString "sha256" (builtins.toJSON m.command);
    } else {
      command = m.command;
      environment = m.environment;
    } // lib.optionalAttrs (m.url != null) { url = m.url; });

  configFile = toml.generate "timeshare.toml" (lib.recursiveUpdate {
    listen = "${if lib.hasInfix ":" cfg.host then "[${cfg.host}]" else cfg.host}:${toString cfg.port}";
    state_dir = stateDir;
    systemctl = [ "${config.systemd.package}/bin/systemctl" ];
    tls = lib.optionalAttrs cfg.tls.enable { cert = certFile; key = keyFile; };
    models = lib.mapAttrs modelSettings cfg.models;
  } cfg.settings);

  admin = pkgs.writeShellScriptBin "gpu-timeshare-admin" ''
    exec ${lib.getExe cfg.package} "$@" --config ${configFile}
  '';

  hasProcessGpu = lib.any (m: m.isolation == "process" && m.gpu) (lib.attrValues cfg.models);
in
{
  options.services.gpu-timeshare = {
    enable = lib.mkEnableOption "gpu-timeshare, many models taking turns on one GPU behind the OpenAI API";

    package = mkOption {
      type = types.package;
      default = pkgs.gpu-timeshare or (import ../default.nix { inherit pkgs; });
      defaultText = lib.literalMD "`pkgs.gpu-timeshare`, or this repository's";
      description = "gpu-timeshare.";
    };

    host = mkOption {
      type = types.str;
      default = "127.0.0.1";
      description = "Address the API listens on.";
    };

    port = mkOption {
      type = types.port;
      default = 8100;
      description = "Port the API listens on.";
    };

    openFirewall = mkOption {
      type = types.bool;
      default = false;
      description = "Open the port (set `host` to something other than loopback too).";
    };

    tls = {
      enable = mkOption {
        type = types.bool;
        default = !loopback;
        defaultText = lib.literalMD "on unless `host` is loopback";
        description = "Serve https: a token is a password, and requests carry whatever they carry.";
      };
      certFile = mkOption {
        type = types.nullOr types.path;
        default = null;
        description = ''
          The certificate (PEM), re-read whenever it changes -- a renewal
          needs no restart; the gpu-timeshare user must be able to read it
          and the key. null: a self-signed one for `tls.hosts`, made on the
          first start in ${tlsDir}/timeshare.crt, which clients then trust
          as their CA. Delete both files there to remake it.
        '';
      };
      keyFile = mkOption {
        type = types.nullOr types.path;
        default = null;
        description = "The certificate's private key (PEM), with `tls.certFile`.";
      };
      hosts = mkOption {
        type = types.listOf types.str;
        default = lib.unique ([ config.networking.hostName config.networking.fqdnOrHostName "localhost" "127.0.0.1" ]
          ++ lib.optional (!loopback && cfg.host != "0.0.0.0" && cfg.host != "::") cfg.host);
        defaultText = lib.literalMD "the host name, its fqdn, localhost, 127.0.0.1 and `host`";
        description = "Names and addresses the self-signed certificate is valid for.";
      };
    };

    models = mkOption {
      type = types.attrsOf (types.submodule modelOptions);
      default = { };
      description = "The models, by the name clients ask for.";
    };

    settings = mkOption {
      type = toml.type;
      default = { };
      example = lib.literalExpression ''
        {
          scheduler = { capacity = 1.0; idle = "10m"; rotation = "2h"; max_attempts = 3; };
          limits = { max_file = "1GiB"; max_window = "7d"; file_retention = "30d"; };
          cache = { enabled = true; max_age = "0"; max_unused = "0"; max_size = "0"; };
        }
      '';
      description = ''
        The rest of timeshare.toml ([scheduler], [limits], [cache],
        endpoints), merged over what the options above produce. Durations
        are Go's ("90s", "10m", "2h") or days ("30d"); sizes take KiB,
        MiB, GiB; 0 means never/unlimited.
      '';
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [{
      assertion = (cfg.tls.certFile == null) == (cfg.tls.keyFile == null);
      message = "services.gpu-timeshare.tls: certFile and keyFile go together";
    }] ++ lib.mapAttrsToList (name: m: {
      assertion = m.isolation == "process" || m.url != null || usesPort m || lib.any (lib.hasInfix "{socket}") m.command;
      message = "services.gpu-timeshare.models.${name}: a unit model listens on {socket} or {port}, or names its url";
    }) cfg.models ++ lib.mapAttrsToList (name: m: {
      assertion = !(m.network && usesPort m);
      message = "services.gpu-timeshare.models.${name}: with network = true it shares the host's loopback; listen on {socket}";
    }) units;
    warnings = lib.optional (!loopback && !cfg.tls.enable)
      "services.gpu-timeshare listens on ${cfg.host} without TLS: tokens cross the network in the clear";

    users.users.gpu-timeshare = {
      isSystemUser = true;
      group = "gpu-timeshare";
      home = stateDir;
      # the models' sockets; process models also want the GPU
      extraGroups = [ socketGroup ] ++ lib.optionals hasProcessGpu [ "video" "render" ];
    };
    users.groups.gpu-timeshare = { };
    users.groups.${socketGroup} = { };

    # setgid: every socket a model makes belongs to the group, and with the
    # models' umask only the group (gpu-timeshare) can connect
    systemd.tmpfiles.settings.gpu-timeshare = {
      ${socketDir}.d = { user = "root"; group = socketGroup; mode = "2770"; };
    };

    environment.systemPackages = [ admin cfg.package ];
    networking.firewall.allowedTCPPorts = lib.mkIf cfg.openFirewall [ cfg.port ];

    # gpu-timeshare may start and stop its model units, and nothing else
    security.polkit.enable = true;
    security.polkit.extraConfig = lib.mkIf (units != { }) ''
      polkit.addRule(function(action, subject) {
        if (action.id == "org.freedesktop.systemd1.manage-units" && subject.user == "gpu-timeshare") {
          var units = ${builtins.toJSON (map (n: "${unitName n}.service") (lib.attrNames units))};
          var verb = action.lookup("verb");
          if (units.indexOf(action.lookup("unit")) >= 0 &&
              (verb == "start" || verb == "stop" || verb == "reset-failed")) {
            return polkit.Result.YES;
          }
        }
      });
    '';

    systemd.services = {
      gpu-timeshare = {
        description = "gpu-timeshare: many models taking turns on one GPU";
        wantedBy = [ "multi-user.target" ];
        after = [ "network.target" "polkit.service" ];
        wants = [ "polkit.service" ];
        environment.XDG_CACHE_HOME = "/var/cache/gpu-timeshare";

        preStart = lib.optionalString selfSigned ''
          mkdir -p ${tlsDir}
          ${lib.getExe cfg.package} cert --if-missing \
            --hosts ${lib.escapeShellArg (lib.concatStringsSep "," cfg.tls.hosts)} \
            --cert ${lib.escapeShellArg certFile} --key ${lib.escapeShellArg keyFile}
        '';

        serviceConfig = {
          ExecStart = "${lib.getExe cfg.package} serve --config ${configFile}";
          User = "gpu-timeshare";
          Group = "gpu-timeshare";
          StateDirectory = "gpu-timeshare";
          StateDirectoryMode = "0700";
          CacheDirectory = "gpu-timeshare";
          WorkingDirectory = stateDir;
          Restart = "on-failure";
          RestartSec = 10;
          # it stops its models on SIGTERM (units through systemd, process
          # models by process group); the rest gets the SIGKILL
          KillMode = "mixed";
          TimeoutStopSec = 120;

          NoNewPrivileges = true;
          PrivateTmp = true;
          ProtectSystem = "strict";
          ProtectHome = true;
          ReadWritePaths = [ socketDir ];
          ProtectKernelTunables = true;
          ProtectKernelModules = true;
          ProtectKernelLogs = true;
          ProtectControlGroups = true;
          ProtectClock = true;
          ProtectHostname = true;
          RestrictSUIDSGID = true;
          RestrictRealtime = true;
          LockPersonality = true;
          CapabilityBoundingSet = "";
          SystemCallArchitectures = "native";
          # AF_UNIX: the system bus (systemctl), the models' sockets
          RestrictAddressFamilies = [ "AF_UNIX" "AF_INET" "AF_INET6" ];
        } // lib.optionalAttrs (!hasProcessGpu) {
          PrivateDevices = true;
        };
      };
    } // lib.mapAttrs' (name: m: lib.nameValuePair (unitName name) {
      description = "gpu-timeshare model ${name}";
      # stopped with the service, never started (or restarted) with it
      unitConfig.StopPropagatedFrom = [ "gpu-timeshare.service" ];
      environment = {
        # vllm, triton, torch and flashinfer compile and cache kernels: kept
        # across runs, it saves minutes per start
        HOME = "/var/cache/gpu-timeshare-models/${name}";
        XDG_CACHE_HOME = "/var/cache/gpu-timeshare-models/${name}";
      } // m.environment;
      serviceConfig = lib.mkMerge [
        {
          # systemd's quoting: % and $ in an argument stay literal
          ExecStart = utils.escapeSystemdExecArgs
            (map (lib.replaceStrings [ "{socket}" "{port}" ] [ (socketOf name) (toString privatePort) ]) m.command);
          # a stale socket from a crash; a proxied model's is the proxy's
          ExecStartPre = lib.mkIf (!usesPort m) "-${pkgs.coreutils}/bin/rm -f ${socketOf name}";
          Restart = "no";
          TimeoutStopSec = 60;
          KillMode = "control-group";

          DynamicUser = true;
          SupplementaryGroups = [ socketGroup ];
          UMask = "0007";
          CacheDirectory = "gpu-timeshare-models/${name}";
          ReadWritePaths = [ socketDir ];
          InaccessiblePaths = [ "-${stateDir}" "-/var/cache/gpu-timeshare" ];
          PrivateTmp = true;
          ProtectSystem = "strict";
          ProtectHome = true;
          ProtectProc = "invisible";
          NoNewPrivileges = true;
          CapabilityBoundingSet = "";
          AmbientCapabilities = "";
          RestrictSUIDSGID = true;
          RestrictRealtime = true;
          RestrictNamespaces = true;
          LockPersonality = true;
          ProtectKernelTunables = true;
          ProtectKernelModules = true;
          ProtectKernelLogs = true;
          ProtectControlGroups = true;
          ProtectClock = true;
          ProtectHostname = true;
          SystemCallArchitectures = "native";
          SystemCallFilter = [ "@system-service" ];
          # AF_NETLINK: interface enumeration (torch.distributed, even on one GPU)
          RestrictAddressFamilies = [ "AF_UNIX" "AF_INET" "AF_INET6" "AF_NETLINK" ];
          # not MemoryDenyWriteExecute: CUDA and triton JIT-compile kernels
        }
        (if m.gpu then {
          DevicePolicy = "closed";
          DeviceAllow = gpuDevices;
        } else {
          PrivateDevices = true;
        })
        (lib.mkIf (!m.network) {
          PrivateNetwork = true;
          IPAddressDeny = "any";
          IPAddressAllow = "localhost";
        })
        m.serviceConfig
      ];
    }) units
    // lib.mapAttrs' (name: m: lib.nameValuePair (proxyName name) {
      description = "gpu-timeshare model ${name}: its socket, relayed to its port";
      requires = [ "${proxyName name}.socket" ];
      after = [ "${proxyName name}.socket" ];
      unitConfig = {
        # its network namespace is the model's, whichever starts first
        JoinsNamespaceOf = [ "${unitName name}.service" ];
        # and it goes with it, so the next start is a fresh namespace
        PartOf = [ "${unitName name}.service" ];
      };
      serviceConfig = {
        ExecStart = "${config.systemd.package}/lib/systemd/systemd-socket-proxyd 127.0.0.1:${toString privatePort}";
        PrivateNetwork = true;
        PrivateTmp = true;
        DynamicUser = true;
        PrivateDevices = true;
        ProtectSystem = "strict";
        ProtectHome = true;
        ProtectProc = "invisible";
        NoNewPrivileges = true;
        CapabilityBoundingSet = "";
        RestrictNamespaces = true;
        LockPersonality = true;
        SystemCallArchitectures = "native";
        SystemCallFilter = [ "@system-service" ];
        RestrictAddressFamilies = [ "AF_UNIX" "AF_INET" "AF_INET6" ];
      };
    }) proxied;

    # a proxied model's socket: made by systemd, connectable only by the
    # socket group (gpu-timeshare); a connection starts the proxy, which
    # finds the model's port refused until gpu-timeshare has started it
    systemd.sockets = lib.mapAttrs' (name: m: lib.nameValuePair (proxyName name) {
      description = "gpu-timeshare model ${name}: its socket";
      wantedBy = [ "sockets.target" ];
      listenStreams = [ (socketOf name) ];
      socketConfig = {
        SocketUser = "root";
        SocketGroup = socketGroup;
        SocketMode = "0660";
      };
    }) proxied;
  };
}
