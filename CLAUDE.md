# gpu-timeshare

GPUs, many models, many tenants, the OpenAI API in front (README.md says what and
why). Go, with cgo for one thing (the scheduler is the Lean model, linked
in), `module gpu-timeshare`; packaged by `default.nix`
(not a flake), with a NixOS module in `nix/module.nix`.

## Layout

- `internal/sched`: `policy.go` is the whole scheduling algorithm in one
  file, its types included (the user wants it in one place, to read beside
  the English and the TLA+): `Decide` (which model on which card, whose
  turn; pure: cards, flows and lines in, actions and lines out) and
  `RoundRobin` (which requests a model that is up gets; the turn's owner
  keeps half the slots, `Owner`; also in Lean, `roundRobin`, and
  `TestCases` holds the two together). `spec/Turns.tla`
  is `Decide`'s TLA+ model. `driver.go` applies them: one `card` per GPU,
  the lines kept in memory, never two requests with the same cache key at
  once.
- `proof/`: the algorithm in Lean 4 (`Timeshare/Policy.lean`: executable,
  imports nothing so `timeshare-check` can link; Mathlib has no objects)
  and proofs about it (`Timeshare/Proofs/`, Mathlib). Every proof file
  ends in `assert_no_sorry`; a new module goes into `Timeshare.lean`.
  To iterate without nix: `lean -o` each module with `LEAN_PATH` set to
  the `.lake/build/lib/lean` of mathlib and its `allLeanDeps`.
- `internal/queue`: the requests not yet delivered, the answer cache
  (key = endpoint + model identity + canonical JSON body), cache
  expiry, `Cache-Control`/`Cache-Status`.
- `internal/batch`: the Files and Batch APIs; a batch's lines are queue
  rows pointing into the input file (offset/length), written to output
  and error files in input order when nothing is left queued or running.
- `internal/upstream`: a model server as a child process (process
  group, killed whole) or a systemd unit (systemctl).
- `internal/api`: HTTP, OpenAI-shaped errors.
- `doc/VERIFICATION.md` (the scheduler: the algorithm, its bounds, its
  TLA+ model and what TLC checked) and
  `doc/SECURITY.md` (the sandbox, its gaps, how to examine it). Change
  them with the code they describe.
- `bin/sandbox-report`: what a running process can reach, from /proc and
  /sys only (`--probe` tests it as the process); packaged as
  `sandbox-report`, and the VM test runs it against a model unit.

## Invariants

- `policy.go`, `spec/Turns.tla`, `proof/Timeshare/Policy.lean` and
  `doc/VERIFICATION.md` §2 are the same algorithm, rule for rule (`[Name]`
  in `policy.go` is the action in the spec; the Lean functions have the Go
  names). Change them together, and run `nix-build -A tests.tla` (TLC) and
  `nix-build -A tests.lean` (the Lean model against Go's decisions) as
  well as `go test ./internal/sched`. TLC found three starvation bugs, a
  double drain and a wrong bound in drafts that looked right on paper
  (VERIFICATION.md, section 9), and proving in Lean that a round ends
  found that `max_timeslice = "0"` hung `Decide`; don't trust a change
  they haven't seen.
- Every defect found in the scheduler, by any means, gets an entry in the
  bug log (VERIFICATION.md §9): the state of the repository then, what
  was wrong, how it showed, the fix (the user's rule: they are useful
  later).
- Turns belong to tenants, not models (the user's call): a tenant must not
  get more of the cards by spreading over models or by queueing more.
- One model per card at a time, deliberately: two busy models sharing a
  card each ran at half speed (measured), so sharing saves only the swap.
  There are no costs or capacity; don't add them back without a
  measurement that says sharing pays. Several cards (`gpus`) are several
  whole cards; a model may be on more than one (a copy), but a copy never
  takes a card it would have to give back, and an idle card doesn't stop
  for one.
- TLC's JVM takes a quarter of the machine's memory by default, and its
  state files are big: run it with `JAVA_TOOL_OPTIONS=-Xmx4g`, a few at a
  time, with `-metadir` on disk and not in a tmpfs. (Eleven at once with
  /tmp as scratch is the likely cause of a session the OOM killer took.)

- The contract with a model is the OpenAI HTTP API, nothing else.
  Don't add per-server special cases.
- `requests` holds only outstanding work: single requests are deleted
  once delivered, batch lines once their batch's files are written.
- Never hold a `*sql.Rows` across another db call or the scheduler's
  mutex (one connection, `SetMaxOpenConns(1)`).
- Answers are cached verbatim; `queue.Present` rewrites `model` (and
  `system_fingerprint`) on the way out, not in the cache.
- A unit model's sandbox is the module's, not the program's: the module
  writes the units, polkit lets the service start/stop exactly those.
  Stop them one `systemctl stop` per unit (polkit refused a multi-unit
  stop in the VM test).
- `queue.Canonical`'s fast path (`internal/queue/canon.go`) must stay
  byte-identical to encoding/json's decode-and-re-encode, or every cache
  key changes. When in doubt it returns errSlow and encoding/json decides;
  `go test -fuzz FuzzCanonical ./internal/queue` holds the two together.

## Tests

`go test ./...` (also inside `nix-build`): end to end against
`gpu-timeshare-stub` (not installed: `-A stub`), unit mode against a
shell-script systemctl.
`nix-build -A tests.tla`: TLC on the scheduler's model (a minute or two;
`spec/big.cfg` by hand takes several).
The scheduler that runs is the Lean model (the user's call, 2026-11-10: the
Go-only build is retired). Three layers, each knowing only its neighbours
(VERIFICATION.md §11): `proof/Timeshare/Export.lean` is the model's
interface as C functions (`@[export lean_ts_*]`, scalars unboxed);
`ffi/schedule.{h,c}` wraps those in plain C structs (`ts_*`; no Lean type
in the header; no knowledge of Lean's layouts in the .c, only reference
counts, which `TestLeanKeepsCount` watches); `internal/sched/lean.go` fills
the structs. No strings-as-protocol: the user rejected the text interface
this began with. `-A scheduler` is `libschedule.a` + `schedule.h` (Policy
and Export through Lean and cc, plus schedule.c; no Mathlib,
so a deployment never builds the proofs) and the driver calls `DecideLean`
and `RoundRobinLean`. `Decide` and `RoundRobin` in `policy.go` stay as the
page to read and as what `TestLeanAgrees` and `TestLeanRoundRobinAgrees`
compare with: keep them in step. `go test` needs the library, so run it in
`nix-shell`. A caller must not pass its own `pkgs`: the Lean and Mathlib
the proofs are checked with are the pin's.
`nix-build -A proof` type-checks the Lean proofs; `nix-build -A tests.lean`
also runs the Lean model on every round `TestCases` writes (seconds, once
Mathlib is in the store: 1.6 GB).
`nix-build -A tests.nixos`: the module in a VM, the official OpenAI
Python SDK over TLS, the sandbox probed from inside (the stub's
`--probe-read`/`--probe-dial`) against a process-mode control.
No GPU anywhere in the tests; the GPU device rules are untested until
the module runs on a machine with one.
