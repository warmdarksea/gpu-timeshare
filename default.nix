# gpu-timeshare, for nix (not a flake):
#
#   nix-build                       gpu-timeshare (and gpu-timeshare-stub, the fake model server the tests use)
#   nix-build -A tests.nixos        a VM: the module, sandboxed model units, an OpenAI SDK client over TLS
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
    };
    meta = {
      description = "One GPU, many models, the OpenAI API in front: batches, a queue, a cache, and taking turns";
      mainProgram = "gpu-timeshare";
      platforms = lib.platforms.linux;
    };
  };
in
gpu-timeshare
