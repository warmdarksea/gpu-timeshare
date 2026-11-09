# gpu-timeshare, for nix (not a flake):
#
#   nix-build                       gpu-timeshare (and gpu-timeshare-stub, the fake model server the tests use)
#   nix-build -A tests.nixos        a VM: the module, sandboxed model units, an OpenAI SDK client over TLS
#   nix-build -A tests.tla          TLC checks the scheduler's model (spec/): no model starves
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
    subPackages = [ "cmd/gpu-timeshare" "cmd/gpu-timeshare-stub" ];
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
      tests.nixos = pkgs.testers.runNixOSTest (import ./nix/test.nix { inherit gpu-timeshare; });
      # the scheduler's TLA+ model (spec/): TLC, three to five models and
      # two timings, must find nobody waits past the claimed bound; and one
      # tick under it (tight.cfg) it must find someone who does
      tests.tla = pkgs.runCommand "gpu-timeshare-tla" { nativeBuildInputs = [ pkgs.tlaplus ]; } ''
        cp ${./spec}/* . && chmod u+w *
        sed 's/MaxWait <- Tight/MaxWait <- Claim/' tight.cfg > slow.cfg
        for c in three four five slow; do
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
      description = "One GPU, many models, the OpenAI API in front: batches, a queue, a cache, and taking turns";
      mainProgram = "gpu-timeshare";
      platforms = lib.platforms.linux;
    };
  };
in
gpu-timeshare
