import Lake
open Lake DSL

package «timeshare-model»

-- Provided by nix (leanPackages.mathlib) via buildLakePackage's leanDeps;
-- never fetched or built by lake itself.
require "leanprover-community" / "mathlib" @ git "main"

-- The scheduler itself: the model (Timeshare.Policy, which imports nothing)
-- and its text interface. Built as a static library, libScheduler.a, that a
-- program in another language links (the Go program does, with
-- `-tags leansched`): `timeshare_decide` is `Decide`.
@[default_target]
lean_lib Scheduler where
  globs := #[.one `Timeshare.Policy, .one `Timeshare.Text]
  defaultFacets := #[LeanLib.staticFacet]

-- The proofs about it. Building this library is what type-checks them.
@[default_target]
lean_lib Timeshare where
  globs := #[.one `Timeshare, .submodules `Timeshare.Proofs]

-- The model against the Go code's decisions. It imports only the
-- scheduler: nixpkgs' mathlib has no objects to link against.
@[default_target]
lean_exe «timeshare-check» where
  root := `Check
