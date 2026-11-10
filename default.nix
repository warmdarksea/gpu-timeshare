# gpu-timeshare, for nix (not a flake):
#
#   nix-build                       gpu-timeshare (one command; -A stub is the fake model server the tests use).
#                                   Its scheduler is the Lean model of proof/, compiled and linked in (cgo).
#   nix-build -A tests.nixos        a VM: the module, sandboxed model units, an OpenAI SDK client over TLS
#   nix-build -A tests.lean         the Lean model (proof/) decides as the Go code does; -A proof checks the proofs
#   nix-build -A tests.tla          TLC checks the scheduler's model (spec/): no flow starves
#   nix-shell                       go, with the Lean scheduler to link: go test ./...
#
# The NixOS module is `module` (nix/module.nix). From another flake or
# config:
#   ts = import gpu-timeshare-src { inherit (pkgs.stdenv.hostPlatform) system; };
#   imports = [ ts.module ];   services.gpu-timeshare.package = ts;
# Leave `pkgs` to the pin below: the proofs are checked against one Lean
# and one Mathlib, and another nixpkgs has others.
{
  system ? builtins.currentSystem,
  pkgs ? import (builtins.fetchTarball {
    url = "https://releases.nixos.org/nixpkgs/nixpkgs-26.11pre1107841.9d3b8db48266/nixexprs.tar.zst";
    sha256 = "sha256-WqewjvVjGQ1yhAvxeZW7IKoIT08vUNfyaeZewOwyYxg=";
  }) { inherit system; config = { }; overlays = [ ]; },
}:
let
  inherit (pkgs) lib;

  # what Lean's runtime links
  leanLibs = [ pkgs.gmp pkgs.libuv pkgs.stdenv.cc.cc.lib ];

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
    subPackages = [ "cmd/gpu-timeshare" ];
    ldflags = [ "-s" "-w" ];
    # The scheduler is the Lean model (proof/, doc/VERIFICATION.md §8): its
    # static library (`scheduler` below), linked in through cgo with Lean's
    # runtime, so that the functions the theorems are about are the ones
    # that run (internal/sched/lean.go).
    buildInputs = leanLibs;
    env.CGO_ENABLED = "1";
    env.CGO_CFLAGS = "-I${pkgs.leanPackages.lean4}/include";
    env.CGO_LDFLAGS = lib.concatStringsSep " " ([
      "${gpu-timeshare.scheduler}/lib/libscheduler.a"
      "-L${pkgs.leanPackages.lean4}/lib/lean"
      "-lInit" "-lleanrt" "-lstdc++" "-lgmp" "-luv" "-lm" "-ldl" "-lpthread"
    ] ++ map (l: "-Wl,-rpath,${lib.getLib l}/lib") leanLibs);
    # every package's tests, end to end included (the stub stands in for
    # the model servers; a shell script for systemctl). The test binaries,
    # and the stub the tests build, are linked outside the wrapper that
    # gives the installed one its rpath.
    checkPhase = ''
      runHook preCheck
      export LD_LIBRARY_PATH=${lib.makeLibraryPath leanLibs}
      go test ./...
      unset LD_LIBRARY_PATH
      runHook postCheck
    '';
    doInstallCheck = true;
    installCheckPhase = ''
      $out/bin/gpu-timeshare help > /dev/null 2>&1 || $out/bin/gpu-timeshare --help > /dev/null 2>&1 || {
        $out/bin/gpu-timeshare help; exit 1; }
    '';
    passthru = {
      module = ./nix/module.nix;
      # the fake model server the tests use: not installed with gpu-timeshare
      # (one command there), built on its own for the VM test
      stub = gpu-timeshare.overrideAttrs (old: {
        pname = "gpu-timeshare-stub";
        subPackages = [ "cmd/gpu-timeshare-stub" ];
        doCheck = false;
        doInstallCheck = false;
        # no scheduler in it: no cgo, nothing of Lean's to find at run time
        env = old.env // { CGO_ENABLED = "0"; CGO_CFLAGS = ""; CGO_LDFLAGS = ""; };
        buildInputs = [ ];
        meta = old.meta // { mainProgram = "gpu-timeshare-stub"; };
      });
      # bin/sandbox-report, with its interpreter: what a process can reach
      # (doc/SECURITY.md)
      sandbox-report = pkgs.runCommand "sandbox-report" { } ''
        mkdir -p $out/bin
        { echo "#!${pkgs.python3}/bin/python3"; tail -n +3 ${./bin/sandbox-report}; } > $out/bin/sandbox-report
        chmod 755 $out/bin/sandbox-report
      '';
      # libscheduler.a: the Lean model (proof/Timeshare/Policy.lean) and its
      # text interface (Text.lean), compiled to C by Lean and to objects by
      # cc. Neither file imports anything, so this needs Lean and not
      # Mathlib -- which `proof` does, and which no binary cache has: a
      # machine that only runs gpu-timeshare builds this in seconds and
      # never the proofs. They are the same two files `proof` checks the
      # theorems against.
      scheduler = pkgs.runCommandCC "timeshare-scheduler" { nativeBuildInputs = [ pkgs.leanPackages.lean4 ]; } ''
        mkdir -p Timeshare build/Timeshare $out/lib
        cp ${./proof/Timeshare/Policy.lean} Timeshare/Policy.lean
        cp ${./proof/Timeshare/Text.lean} Timeshare/Text.lean
        for m in Policy Text; do
          LEAN_PATH=build lean -o build/Timeshare/$m.olean -c build/$m.c Timeshare/$m.lean
          $CC -c -O3 -DNDEBUG -fPIC -I${pkgs.leanPackages.lean4}/include -o build/$m.o build/$m.c
        done
        $AR rcs $out/lib/libscheduler.a build/Policy.o build/Text.o
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
          export LD_LIBRARY_PATH=${lib.makeLibraryPath leanLibs}
          TIMESHARE_CASES=$NIX_BUILD_TOP/cases go test ./internal/sched -run '^TestCases$'
        '';
        doCheck = false;
        doInstallCheck = false;
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
