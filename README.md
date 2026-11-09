> slop alert: llm-generated prose follows. sorry. -norn

# gpu-timeshare

One GPU, many models, the OpenAI API in front.

You have more models than fit on the card at once. A server that loads
whichever model each request names would spend its time reloading weights
whenever requests for different models interleave. gpu-timeshare queues
the requests, lets the loaded model answer everything queued for it, and
only then swaps. Any OpenAI client works with it unchanged, and so does a
batch.

- **The OpenAI API.** `/v1/chat/completions` (and any other endpoint you
  list), `/v1/models`, `/v1/files` and `/v1/batches`. Point an OpenAI SDK
  at it with a token as the API key.
- **Taking turns, without starving anyone.** One model has the card at
  a time. Once it has had it for `max_timeslice` while another model
  waits, it drains and leaves, and the model whose turn it is loads. A
  TLA+ model of the scheduler, checked by TLC, shows every model with
  work is served within *n* turns (see [The scheduler](#the-scheduler)). Within a model, clients take turns
  round-robin, and each client's requests go oldest first (single
  requests ahead of batch lines: someone is holding a connection open for
  those).
- **Idle unload.** A model with no work for `idle` stops, so an empty
  queue leaves nothing on the card and it can drop to its idle power state.
- **A cache.** Every answer is kept verbatim, keyed by the question: the
  endpoint, the model's identity (its weights) and the request body as
  canonical JSON. The same question costs no GPU the second time,
  whoever asks it. Two identical requests in flight are asked only once.
- **Batches.** OpenAI's Batch API, with OpenAI's rules: one model per batch,
  so a client written for OpenAI works here unchanged. Batches for several
  models, queued together, are answered one model at a time. Output comes back
  in input order.
- **What a model is:** any server that speaks the OpenAI HTTP API: vLLM,
  llama.cpp's server, SGLang, TGI, Ollama, or a wrapper of your own. It is
  either a command gpu-timeshare runs, or a systemd unit it starts and
  stops. With the NixOS module, each model gets its own sandboxed unit.

## Using it

```python
from openai import OpenAI
c = OpenAI(base_url="https://gpu-box:8100/v1", api_key="gts_...")
c.chat.completions.create(model="qwen", messages=[...])

f = c.files.create(file=open("requests.jsonl", "rb"), purpose="batch")
b = c.batches.create(input_file_id=f.id, endpoint="/v1/chat/completions", completion_window="24h")
# poll c.batches.retrieve(b.id) until "completed", then c.files.content(b.output_file_id)
```

A single request waits for its model's turn, which can mean minutes while
the model loads, so give your client a generous timeout. Nothing is
streamed: `stream: true` is refused.

**Where this differs from OpenAI:**
- `completion_window` is any duration up to `limits.max_window`, not only `24h`;
- the only file purpose accepted is `batch`.

### The cache, over plain HTTP

Send `Cache-Control` (RFC 9111) on a request. On a batch's create, it
applies to every line.

| directive | effect |
|---|---|
| `no-cache` | asks the model even if an answer is cached; the new answer is stored |
| `no-store` | asks the model, and doesn't store the answer |
| `max-age=N` | accepts a cached answer only if it's at most N seconds old |
| `only-if-cached` | answers from the cache or not at all (`504`, code `not_cached`); never starts a model |

Every answer says where it came from in `Cache-Status` (RFC 9211):

| value | meaning |
|---|---|
| `gpu-timeshare; hit` | from the cache; `Age` gives how old it is |
| `gpu-timeshare; fwd=miss; stored` | asked of the model and kept |
| `gpu-timeshare; fwd=request` | asked because the request said so; `; stored` if it was kept |
| `gpu-timeshare; fwd=miss; collapsed` | the same question was already being asked, and this got that answer |

In a batch's output file, each line's `response.cache_status` carries the
same value. With the Python SDK, pass the request header as
`extra_headers={"Cache-Control": "no-cache"}` and read the response header
from `.with_raw_response`.

The cache key covers the model's `fingerprint`, which defaults to the
command that runs it. On nix that command names the weights' store path,
so new weights get new cache entries. A model with non-deterministic
sampling still gets its first answer cached; send `no-cache` when you want
a fresh sample.

## Configuration

`gpu-timeshare serve --config timeshare.toml`. Every setting below is shown
with its default, except the models:

```toml
listen    = "127.0.0.1:8100"
state_dir = "."                       # timeshare.db, files/, logs/, run/ (the models' sockets)
systemctl = ["systemctl"]             # for models run as units; ["systemctl", "--user"] for a user manager
endpoints = ["/v1/chat/completions", "/v1/completions", "/v1/embeddings"]

[tls]                                 # both, or neither; re-read when they change
cert = ""
key  = ""

[scheduler]
idle            = "10m"               # stop a model after this long with no work (0: never)
max_timeslice   = "2h"                # the model on the card gives way this long after loading, if another waits
max_attempts    = 3                   # per request: a failed connection, a 5xx or a 429 counts
start_timeout   = "15m"
request_timeout = "10m"
stop_grace      = "30s"               # SIGTERM to SIGKILL, for commands
broken_for      = "5m"                # after failing twice, a model's requests fail for this long

[limits]
max_body        = "64MiB"
max_file        = "1GiB"
max_batch_lines = 50000
max_window      = "7d"
file_retention  = "30d"               # uploads and results are deleted after this (0: kept)

[cache]
enabled    = true
max_age    = "0"                      # drop answers older than this (0: never)
max_unused = "0"                      # drop answers not served for this long
max_size   = "0"                      # drop the least recently used past this

[models.qwen]
command     = ["vllm", "serve", "/models/qwen", "--uds", "{socket}", "--gpu-memory-utilization", "0.95"]
concurrency = 8                       # requests in flight to it
# ready = "/v1/models"                # answers 200 once it's up
# upstream_model = "..."              # default: the first model its /v1/models lists
# fingerprint = "..."                 # default: derived from the command
# start_timeout, cache = false, environment = { K = "v" }

[models.pixai]
unit = "pixai.service"                # a systemd unit instead of a command
url  = "unix:/run/pixai.sock"         # where it answers (http://host:port or unix:/path)
```

In a command, `{socket}` becomes a unix socket under `state_dir/run`, and
`{port}` becomes a free TCP port on 127.0.0.1. A unix socket is the better
choice: on a TCP port, any local user can reach the model without a
token. vLLM listens on one with `--uds`. (With the NixOS module, each model
unit has a loopback of its own, so `{port}` is safe there too.)

### Clients

```
gpu-timeshare token add alice [--admin]   # prints alice's token, once; only its sha256 is kept
gpu-timeshare token list | remove NAME
gpu-timeshare cache stats | clear [--model NAME]
gpu-timeshare check                       # reads the config, says what it found
gpu-timeshare cert --hosts box,10.0.0.2   # a self-signed certificate (its own CA) for [tls]
```

A client sees its own files and batches; an admin sees everyone's.
Answers are shared through the cache. Getting a cached answer means
sending the whole question again, image bytes included, so holding the
question is the permission.

`GET /v1/timeshare/status` shows each model's state, queue and requests
in flight. `GET /health` answers with no token.

## The scheduler

Two levels. Which model has the card is `Decide`
(`internal/sched/policy.go`, one page). Which requests a loaded model gets
is round-robin between clients, oldest first within each.

**One model has the card at a time.** Two models can share it if they fit,
but sharing buys nothing when both are busy: measured on a 3090 with two
vLLM servers that fit side by side (deepseek-ocr and joycaption), each ran
at 49% of its speed alone, 98% of one model's work between them. The GPU
takes turns between processes; it doesn't run them at once. Sharing only
saves the swap, and with one model at a time there are no sizes to get
right. So each model can have the whole card (for vLLM:
`--gpu-memory-utilization 0.9` or so, a bigger KV cache).

Each round:

1. A draining model with nothing in flight stops.
2. A model with nothing to do stops, at once if another model is waiting,
   or after `idle`.
3. A model that loaded `max_timeslice` ago, while another model waits,
   drains: it finishes what it's doing and takes nothing new.
4. If the card is free, the waiting model whose **turn** it is starts: the
   one that loaded longest ago (never counts as longest).

**The guarantee.** Take *n* models, and say a turn lasts at most a load,
`max_timeslice` and a drain. Then a model with work is served (loaded, with
the card for `max_timeslice`) within *n* − 1 turns, plus its own drain if it
was on the card and its own load, unless its work runs out first. However
hostile the loads, drains and arriving work are: a load is at most
`start_timeout` and a drain at most `request_timeout`, so the worst case is
about (*n* − 1) × (`max_timeslice` + `start_timeout` + `request_timeout`);
with loads of a few minutes, it is about (*n* − 1) × `max_timeslice`. The
bound is tight: TLC finds a model that waits exactly that long.

`spec/Timeslice.tla` is the same algorithm in TLA+, rule for rule (the
`[Name]` comments in `policy.go` are its actions). `nix-build -A tests.tla`
has TLC check the guarantee against every interleaving for three, four and
five models (seconds; six take a few minutes), and check that one tick
less is violated. `TestNoStarvation` checks the same bound against
`Decide` itself, in 500 random worlds, and that two models are never on
the card at once.

## NixOS

`nix/module.nix` (`(import ./. {}).module`) is `services.gpu-timeshare`.
Each model is its own systemd unit, `gpu-timeshare-model-NAME`. Only
gpu-timeshare starts those units, and a polkit rule lets it start and stop
exactly those units and nothing else. The sandbox:

- a throwaway user per run;
- a read-only file system, apart from the model's own cache directory;
- no access to gpu-timeshare's state;
- the nvidia device nodes and no other devices;
- a network namespace of its own: a private loopback, nothing beyond it (`network = true` gives it the host's);
- a server that only does TCP listens on `{port}` on that private loopback, and `systemd-socket-proxyd`, in the same namespace, relays its unix socket to it;
- no capabilities;
- the `@system-service` syscalls;
- the model's socket is reachable only by gpu-timeshare;
- stopping a model stops its whole cgroup, so a stopped model never leaves VRAM behind.

```nix
services.gpu-timeshare = {
  enable = true;
  host = "0.0.0.0";          # TLS turns itself on off loopback (self-signed unless tls.certFile)
  openFirewall = true;
  settings.scheduler.idle = "10m";
  models.qwen = {
    command = [ "${vllm}/bin/vllm" "serve" "${weights}" "--uds" "{socket}" ];
    concurrency = 8;
    serviceConfig.MemoryMax = "64G";   # merged into the unit
  };
};
```

Make tokens with `sudo -u gpu-timeshare gpu-timeshare-admin token add alice`.
Clients trust `/var/lib/gpu-timeshare/tls/timeshare.crt`.

## Building and testing

```
nix-build                    # gpu-timeshare, gpu-timeshare-stub; the go tests run in the build
nix-build -A tests.nixos     # VM: the module, sandboxed units, the OpenAI SDK over TLS
nix-build -A tests.tla       # TLC: the scheduler's model starves no one
go test ./...                # the same go tests, no nix needed
```

The Go tests run the real API and scheduler against `gpu-timeshare-stub`, a
fake OpenAI server that starts slowly, can be made to fail, crash or fork
a child, and logs every request. Among other things, they check:
- batches for two models from two clients, queued at once, are answered
  with exactly one model switch;
- no model ever has more requests in flight than its `concurrency`;
- an idle unload takes the model's forked children with it;
- expiry, cancellation and a crashing model all end their batches;
- unit mode works, against a fake `systemctl`.

The VM test drives the module with the official Python SDK and checks the
sandbox from outside: from inside its unit, the model can't read the
service's database or connect to another machine on the network.
