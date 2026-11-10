# gpu-timeshare, for nix (not a flake):
#
#   nix-build                       gpu-timeshare (one command; -A stub is the fake model server the tests use)
#   nix-build -A tests.nixos        a VM: the module, sandboxed model units, an OpenAI SDK client over TLS
#   nix-build -A tests.lean         the Lean model (proof/) decides as the Go code does; -A proof checks the proofs
#   nix-build -A tests.tla          TLC checks the scheduler's model (spec/): no flow starves
#   nix-shell                       go, gopls
#
# The NixOS module is `module` (nix/module.nix). From another flake or
# config:
#   ts = import gpu-timeshare-src { inherit pkgs; };
#   imports = [ ts.module ];   services.gpu-timeshare.package = ts;
{
  system ? builtins.currentSystem,
  pkgs ? import (builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1107841.9d3b8db48266/nixexprs.tar.zst";
    sha256 = "sha256-WqewjvVjGQ1yhAvxeZW7IKoIT08vUNfyaeZewOwyYxg=";
  }) { inherit system; config = { }; overlays = [ ]; },
}:
let
  inherit (pkgs) lib;

  gpu-timeshare = pkgs.buildGoModule {
    pname = "gpu-timeshare";
    version = "0.1.0";
    # only what the go build reads, so editing nix files rebuilds nothing
    src = lib.fileset.toSource {
      root = ./.;
      fileset = lib.fileset.unions [
        ./go.mod
        ./go.sum
        (lib.fileset.fileFilter (f: f.hasExt "go") ./.)
      ];
    };
    vendorHash = "sha256-oiFR2zSOSg5J4G78BuisXU4S/1/dqOZ4ZZRm0RSjJmA=";
    env.CGO_ENABLED = "0";
    subPackages = [ "cmd/gpu-timeshare" ];
    ldflags = [ "-s" "-w" ];
    # every package's tests, end to end included (the stub stands in for
    # the model servers; a shell script for systemctl)
    checkPhase = ''
      runHook preCheck
      go test ./...
      runHook postCheck
    '';
    passthru = {
      module = ./nix/module.nix;
      # the fake model server the tests use: not installed with gpu-timeshare
      # (one command there), built on its own for the VM test
      stub = gpu-timeshare.overrideAttrs (old: {
        pname = "gpu-timeshare-stub";
        subPackages = [ "cmd/gpu-timeshare-stub" ];
        doCheck = false;
        meta = old.meta // { mainProgram = "gpu-timeshare-stub"; };
      });
      # bin/sandbox-report, with its interpreter: what a process can reach
      # (doc/SECURITY.md)
      sandbox-report = pkgs.runCommand "sandbox-report" { } ''
        mkdir -p $out/bin
        { echo "#!${pkgs.python3}/bin/python3"; tail -n +3 ${./bin/sandbox-report}; } > $out/bin/sandbox-report
        chmod 755 $out/bin/sandbox-report
      '';
      # The scheduler in Lean (proof/, doc/VERIFICATION.md §8): the model and the
      # proofs about it. Building it type-checks them; a `sorry` fails the build
      # (assert_no_sorry). Mathlib comes from nixpkgs, never from lake.
      proof = pkgs.leanPackages.buildLakePackage {
        pname = "timeshare-model";
        version = "0.1.0";
        src = lib.fileset.toSource {
          root = ./proof;
          fileset = lib.fileset.unions [
            ./proof/lakefile.lean
            ./proof/lake-manifest.json
            (lib.fileset.fileFilter (f: f.hasExt "lean") ./proof)
          ];
        };
        leanDeps = [ pkgs.leanPackages.mathlib ];
        meta.mainProgram = "timeshare-check";
      };
      # every round of a few hundred simulated worlds: what Go's Decide was
      # given and what it answered (internal/sched/cases_test.go)
      cases = gpu-timeshare.overrideAttrs (old: {
        pname = "gpu-timeshare-cases";
        buildPhase = ''
          TIMESHARE_CASES=$NIX_BUILD_TOP/cases go test ./internal/sched -run '^TestCases$'
        '';
        doCheck = false;
        installPhase = "cp $NIX_BUILD_TOP/cases $out";
        dontFixup = true;
      });
      # the Lean model must decide every one of those rounds as Go did, and
      # every module of proof/ must have been checked
      tests.lean = pkgs.runCommand "gpu-timeshare-lean" { } ''
        for f in $(cd ${./proof} && find . -name "*.lean" ! -name lakefile.lean ! -name Check.lean); do
          test -e ${gpu-timeshare.proof}/.lake/build/lib/lean/''${f%.lean}.olean || { echo "$f was not checked"; exit 1; }
        done
        ${gpu-timeshare.proof}/bin/timeshare-check ${gpu-timeshare.cases} | tee $out
      '';
      tests.nixos = pkgs.testers.runNixOSTest (import ./nix/test.nix { inherit gpu-timeshare; });
      # the scheduler's TLA+ model (spec/, doc/VERIFICATION.md): TLC must
      # find every invariant true in each configuration -- one card and
      # two, up to three tenants and three models -- and, one tick under
      # the claimed bound (tight.cfg), a flow that waits longer
      tests.tla = pkgs.runCommand "gpu-timeshare-tla" { nativeBuildInputs = [ pkgs.tlaplus ]; } ''
        cp ${./spec}/* . && chmod u+w *
        export JAVA_TOOL_OPTIONS="-Xmx4g -Djava.io.tmpdir=$TMPDIR"
        for c in t3m1 t1m3 t2m2 t3m2 t2m3 one g2; do
          echo "== $c"
          tlc -workers auto -config $c.cfg -metadir $TMPDIR/$c MC.tla > $c.log 2>&1 || { cat $c.log; exit 1; }
          grep -q "No error has been found" $c.log || { cat $c.log; exit 1; }
          grep "distinct states found" $c.log
        done
        echo "== tight (must fail)"
        if tlc -workers auto -config tight.cfg -metadir $TMPDIR/t MC.tla > t.log 2>&1; then cat t.log; exit 1; fi
        grep -q "Invariant Bounded is violated" t.log || { cat t.log; exit 1; }
        touch $out
      '';
    };
    meta = {
      description = "GPUs, many models and tenants, the OpenAI API in front: batches, a queue, a cache, and taking turns";
      mainProgram = "gpu-timeshare";
      platforms = lib.platforms.linux;
    };
  };
in
gpu-timeshare
