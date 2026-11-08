# The module in a VM, with gpu-timeshare-stub as the models (no GPU here):
# a client machine drives it with the official OpenAI Python SDK over TLS,
# and the test checks the sandbox from the outside -- what a model can't
# read, can't reach, and what gpu-timeshare can't make systemd do.
{ gpu-timeshare }:
let
  stub = "${gpu-timeshare}/bin/gpu-timeshare-stub";
in
{
  name = "gpu-timeshare";

  nodes.server = { ... }: {
    imports = [ gpu-timeshare.module ];
    services.gpu-timeshare = {
      enable = true;
      package = gpu-timeshare;
      host = "0.0.0.0";
      openFirewall = true;
      settings.scheduler.idle = "4s";
      models.a = {
        command = [ stub "--uds" "{socket}" "--name" "upstream-a" "--start" "1s"
          "--probe-read" "/var/lib/gpu-timeshare/timeshare.db,/etc/hostname"
          "--probe-dial" "192.168.1.1:8080" ];
        cost = 0.6;
        concurrency = 2;
        gpu = false;
      };
      models.b = {
        command = [ stub "--uds" "{socket}" "--name" "upstream-b" "--start" "1s" "--child" ];
        cost = 0.6;
        gpu = false;
      };
      # a child process, not a unit
      models.p = {
        isolation = "process";
        # the control for a's probe: outside the units' sandbox, the same dial works
        command = [ stub "--port" "{port}" "--name" "upstream-p" "--start" "0s" "--probe-dial" "192.168.1.1:8080" ];
        cost = 0.1;
        gpu = false;
      };
    };
  };

  nodes.client = { pkgs, ... }: {
    environment.systemPackages = [ (pkgs.python3.withPackages (ps: [ ps.openai ps.httpx ])) ];
    environment.etc."sdk_test.py".source = ./sdk_test.py;
    networking.firewall.allowedTCPPorts = [ 8080 ];
  };

  testScript = ''
    start_all()
    server.wait_for_unit("gpu-timeshare.service")
    server.wait_for_open_port(8100)
    client.wait_for_unit("multi-user.target")
    # something on the network for a model's probe to try to reach
    client.succeed("systemd-run --unit probe-target python3 -m http.server 8080")
    client.wait_for_open_port(8080)
    server.succeed("curl -sf http://192.168.1.1:8080/ >/dev/null")  # reachable, for the server itself

    token = server.succeed("runuser -u gpu-timeshare -- gpu-timeshare-admin token add alice").strip()
    assert token.startswith("gts_"), token
    crt = server.succeed("cat /var/lib/gpu-timeshare/tls/timeshare.crt")
    client.succeed(f"cat > /tmp/ca.crt <<'EOF'\n{crt}EOF")
    print(client.succeed(f"TOKEN={token} python3 /etc/sdk_test.py https://server:8100/v1 /tmp/ca.crt"))

    with subtest("the model's sandbox"):
        journal = server.succeed("journalctl -u gpu-timeshare-model-a -o cat")
        assert "probe read /etc/hostname: ok" in journal, journal
        assert "probe read /var/lib/gpu-timeshare/timeshare.db: ERROR" in journal, journal
        assert "probe dial 192.168.1.1:8080: ERROR" in journal, journal
        control = server.succeed("cat /var/lib/gpu-timeshare/logs/p.log")
        assert "probe dial 192.168.1.1:8080: ok" in control, control
        assert "Access denied" not in server.succeed("journalctl -u gpu-timeshare -o cat"), "the start-up stop of the units was refused"
        props = server.succeed("systemctl show gpu-timeshare-model-a -p DynamicUser -p NoNewPrivileges -p PrivateDevices -p CapabilityBoundingSet")
        assert "DynamicUser=yes" in props and "NoNewPrivileges=yes" in props and "PrivateDevices=yes" in props, props
        # only gpu-timeshare (and root) can connect to a model's socket
        server.succeed("stat -c '%G %a' /run/gpu-timeshare-models | grep -x 'gpu-timeshare-models 2770'")

    with subtest("polkit: its own units, nothing else"):
        server.fail("runuser -u gpu-timeshare -- systemctl stop nscd.service")
        server.succeed("systemctl is-active nscd.service")

    with subtest("idle: the models stop, with their children"):
        server.wait_until_fails("systemctl is-active gpu-timeshare-model-a.service", timeout=60)
        server.wait_until_fails("systemctl is-active gpu-timeshare-model-b.service", timeout=60)
        server.fail("pgrep -f 'sleep 3600'")

    with subtest("a restart starts no model, and keeps the certificate"):
        before = server.succeed("sha256sum /var/lib/gpu-timeshare/tls/timeshare.crt")
        server.succeed("systemctl restart gpu-timeshare.service")
        server.wait_for_open_port(8100)
        server.fail("systemctl is-active gpu-timeshare-model-a.service")
        assert before == server.succeed("sha256sum /var/lib/gpu-timeshare/tls/timeshare.crt")
        # and the cache outlived it
        client.succeed(f"TOKEN={token} python3 /etc/sdk_test.py https://server:8100/v1 /tmp/ca.crt cached")
  '';
}
