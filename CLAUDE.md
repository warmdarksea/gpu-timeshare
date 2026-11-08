# gpu-timeshare

One GPU, many models, the OpenAI API in front (README.md says what and
why). Go, cgo off, `module gpu-timeshare`; packaged by `default.nix`
(not a flake), with a NixOS module in `nix/module.nix`.

## Layout

- `internal/sched`: `policy.go` (`Decide`, a pure function of the
  models' states: start smallest-first, stop idle, rotate) and
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

## Invariants

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

## Tests

`go test ./...` (also inside `nix-build`): end to end against
`gpu-timeshare-stub`, unit mode against a shell-script systemctl.
`nix-build -A tests.nixos`: the module in a VM, the official OpenAI
Python SDK over TLS, the sandbox probed from inside (the stub's
`--probe-read`/`--probe-dial`) against a process-mode control.
No GPU anywhere in the tests; the GPU device rules are untested until
the module runs on a machine with one.
