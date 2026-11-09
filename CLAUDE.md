# gpu-timeshare

One GPU, many models, the OpenAI API in front (README.md says what and
why). Go, cgo off, `module gpu-timeshare`; packaged by `default.nix`
(not a flake), with a NixOS module in `nix/module.nix`.

## Layout

- `internal/sched`: `policy.go` (`Decide`: the whole scheduling algorithm,
  one page, a pure function of the models' states; `card.go` its types and
  primitives; `spec/Timeslice.tla` is its TLA+ model) and
  `driver.go` (applies it, dispatches round-robin between clients, never
  two requests with the same cache key at once).
- `internal/queue`: the requests not yet delivered, the answer cache
  (key = endpoint + model identity + canonical JSON body), cache
  expiry, `Cache-Control`/`Cache-Status`.
- `internal/batch`: the Files and Batch APIs; a batch's lines are queue
  rows pointing into the input file (offset/length), written to output
  and error files in input order when nothing is left queued or running.
- `internal/upstream`: a model server as a child process (process
  group, killed whole) or a systemd unit (systemctl).
- `internal/api`: HTTP, OpenAI-shaped errors.
- `doc/DESIGN.md` (the scheduler, its code and its TLA+ model) and
  `doc/SECURITY.md` (the sandbox, its gaps, how to examine it). Change
  them with the code they describe.
- `bin/sandbox-report`: what a running process can reach, from /proc and
  /sys only (`--probe` tests it as the process); packaged as
  `sandbox-report`, and the VM test runs it against a model unit.

## Invariants

- `policy.go` and `spec/Timeslice.tla` are the same algorithm, rule for
  rule (`[Name]` in `Decide` is the action in the spec). Change them
  together, and run `nix-build -A tests.tla` (TLC) as well as
  `TestNoStarvation`.
- One model on the card at a time, deliberately: two busy models sharing
  it each ran at half speed (measured), so sharing saves only the swap.
  There are no costs or capacity; don't add them back without a
  measurement that says sharing pays.

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
`gpu-timeshare-stub`, unit mode against a shell-script systemctl.
`nix-build -A tests.tla`: TLC on the scheduler's model (a few minutes;
`spec/four.cfg` by hand takes longer).
`nix-build -A tests.nixos`: the module in a VM, the official OpenAI
Python SDK over TLS, the sandbox probed from inside (the stub's
`--probe-read`/`--probe-dial`) against a process-mode control.
No GPU anywhere in the tests; the GPU device rules are untested until
the module runs on a machine with one.
