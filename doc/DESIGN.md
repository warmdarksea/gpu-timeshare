# The scheduler

This document describes how gpu-timeshare decides which model has the GPU.
It gives the algorithm in plain words, then the code that implements it,
then the TLA+ model that checks it.

## 1. Terms

| Term | Meaning |
|---|---|
| model | One model server (for example, one vLLM process). |
| the card | The GPU. One model has the card at a time. |
| load | Start a model and wait until it answers. A load can take minutes. |
| drain | Stop sending a model new requests. Let it finish the requests in flight. Then stop it. |
| waiting | A model is waiting when it has queued requests and is not on the card. |
| idle | A model is idle when it is up and has no queued or in-flight requests. |
| `max_timeslice` | How long a model keeps the card after its load, when another model waits. |
| `idle` | How long an idle model stays up when no other model waits. 0 means forever. |
| turn | The order of the waiting models: the model that loaded longest ago is first. A model that never loaded is first of all. Ties go by name. |

## 2. Why one model at a time

Two busy models on one card do not do more work than one model.
We measured this on an RTX 3090 with two vLLM servers that fit on the card together.
Each server ran at 49% of its speed alone.
The GPU takes turns between processes. It does not run them at the same time.
Thus, sharing the card saves only the time to load a model.
With one model at a time, the scheduler does not need model sizes.

## 3. The algorithm

The scheduler does one *round* when something changes (a request arrives,
a model finishes loading, a request ends), and at least every 200 ms.
In each round, it applies these rules to every model:

1. **Drained.** A draining model with no requests in flight stops.
2. **Give way.** An idle model stops immediately if another model waits.
3. **Idle stop.** An idle model stops after `idle`, if no other model waits.
   Then the GPU can go to a low-power state.
4. **Expire.** A busy model drains when another model waits and
   `max_timeslice` has gone by since the model loaded.

After that:

5. **Start.** If no model is on the card and a model waits, the first
   model in the turn starts.

A model's load time is its place in the turn. When a model loads, it goes
to the back of the turn. Thus, the models take the card in rotation.

The rules do not stop a busy model before its `max_timeslice`. They do not
stop a model when no other model waits. Thus, one user with one model
keeps the card for as long as there is work.

### Requests within a model

The rules above decide which model has the card. A second level decides
which requests that model gets:

- Each model has a limit of requests in flight (`concurrency`).
- The scheduler fills free slots round-robin between clients.
- Within one client, the oldest request goes first. A single request goes
  before a batch line, because a client holds a connection open for it.

## 4. The guarantee

Let *n* be the number of models.
Let a *turn* be at most one load, plus `max_timeslice`, plus one drain.

A model with queued requests starts to serve them within:

> (*n* − 1) turns + one drain + one load

unless its queue becomes empty first. The extra drain is for a model that
was on the card and drains while it still has work.

This is true for all request arrivals and for all load and drain times up
to their limits. A load is at most `start_timeout`. A drain is at most
`request_timeout`. With loads of a few minutes, the bound is approximately
(*n* − 1) × `max_timeslice`.

The bound is *tight*. TLC finds a schedule where a model waits for exactly
the bound. Thus, no smaller bound is true (see §6).

## 5. The code

The algorithm is one function, `Decide`, in
[`internal/sched/policy.go`](../internal/sched/policy.go).
`Decide` is pure. It gets the state of each model and the time. It returns
actions: start, stop or drain a model. It changes nothing.

```go
func Decide(models []Model, now time.Time, pol Policy) []Action {
	c := append(Card(nil), models...)   // a copy: a model stopped below is Down for the rest of the round
	turn := c.inTurn()                  // the waiting models, the one that loaded longest ago first
	var out []Action
	for i, m := range c {
		switch {
		case m.State == Draining && m.Inflight == 0:   // rule 1 [Drained]
		case idle(m) && len(turn) > 0:                 // rule 2 [GiveWay]
		case idle(m) && pol.Idle > 0 &&
			now.Sub(m.BusyAt) >= pol.Idle:             // rule 3 [IdleStop]
		case m.State == Up && len(turn) > 0 &&
			now.Sub(m.LoadedAt) >= pol.MaxTimeslice:   // rule 4 [Expire]: drain, not stop
			out = append(out, Action{Drain, m.Name})
			continue
		default:                                       // no rule applies: keep it
			continue
		}
		out = append(out, Action{Stop, m.Name})        // rules 1-3 stop the model
		c[i].State = Down
	}
	if len(turn) > 0 && !c.any(onCard) {               // rule 5 [Start]
		out = append(out, Action{Start, turn[0].Name})
	}
	return out
}
```

The words in brackets are the names of the actions in the TLA+ model.

The primitives are in [`internal/sched/card.go`](../internal/sched/card.go):

```go
func waiting(m Model) bool { return m.State == Down && m.Ready > 0 }                  // queued work, not on the card
func idle(m Model) bool    { return m.State == Up && m.Ready == 0 && m.Inflight == 0 } // up, nothing to do
func onCard(m Model) bool  { return m.State != Down }                                 // starting, up or draining

// inTurn: the waiting models, sorted by LoadedAt (zero, never loaded, is first), then by name
```

The driver, [`internal/sched/driver.go`](../internal/sched/driver.go),
runs `Decide` and does the actions. It keeps one time per model, and that
time is both the model's clock and its place in the turn:

```go
// when the model's server answers (the end of a load):
sl.state, sl.upSince, sl.busyAt = Up, time.Now(), time.Now()

// each round, what Decide gets:
Model{Name: name, State: sl.state, Inflight: sl.inflight, Ready: ready,
	BusyAt: sl.busyAt, LoadedAt: sl.upSince}
```

`Decide` sees one model on the card at most, because rule 5 starts a model
only when the card is empty.

## 6. The TLA+ model

[`spec/Timeslice.tla`](../spec/Timeslice.tla) is the same algorithm in
TLA+. TLC (the TLA+ model checker) examines every possible order of
events and checks two invariants:

- `Alone`: at most one model is on the card.
- `Bounded`: no model waits longer than `MaxWait`.

### How the model relates to the code

| TLA+ | Go | Note |
|---|---|---|
| `st[m]` | `Model.State` | `"down"`, `"starting"`, `"up"`, `"draining"` |
| `work[m]` | `Ready > 0 \|\| Inflight > 0` | Only "has work or not". The number of requests does not change a decision. |
| `order` | sort by `LoadedAt` | `Loaded(m)` moves `m` to the back: `ToBack(m)`. |
| `age` | `now - LoadedAt` of the model on the card | |
| `idle[m]` | `now - BusyAt` | |
| `GiveWay`, `IdleStop`, `Expire`, `Start` | rules 2, 3, 4, 5 | The scheduler's actions. |
| `Drained` | rule 1 | Done in one step with the end of the drain. |
| `Loaded`, `Arrive`, `Done` | the model server, the clients | Not the scheduler: TLC tries every possible order. |
| `Tick` | time | One unit of time. |
| `MaxLoad`, `MaxDrain` | `start_timeout`, `request_timeout` | |

### What the model assumes

- **Time is discrete.** `Tick` adds one unit of time.
- **The scheduler takes no time.** `Tick` is not possible while a
  scheduler action is possible (`~ENABLED Decide`). The code does the same:
  a round applies all rules before time goes on.
- **Everything else is an adversary.** Requests arrive and end at any time.
  A load takes any time up to `MaxLoad`. A drain takes any time up to
  `MaxDrain` (`Overdue` forces the end at the limit).
- **One model is watched.** `watched` is any one model, chosen in `Init`.
  `wait` counts the ticks when it has work but does not serve: it is off
  the card, loading or draining. `wait` goes to 0 when the model loads,
  or when its work ends. Because `Init` tries every model as `watched`,
  the invariant is true for all models.

### What the model does not include

- Per-client round-robin within a model (§3, "Requests within a model").
  It does not change which model has the card.
- A model that fails to start. The driver refuses its requests for
  `broken_for`, so it is not waiting. This removes a model from the turn;
  it cannot make another model wait longer.
- The real request counts and durations. Only "has work or not" is in
  the model.

### The bound in TLA+

[`spec/MC.tla`](../spec/MC.tla) defines the bound from §4:

```tla
Turn1 == MaxLoad + MaxTimeslice + MaxDrain
Claim == (Cardinality(Models) - 1) * Turn1 + MaxDrain + MaxLoad
Tight == Claim - 1      \* TLC must find a violation of this one
```

### The checks

`nix-build -A tests.tla` runs TLC on these configurations:

| Config | Models | `MaxTimeslice`, `MaxLoad`, `MaxDrain` | `MaxWait` | Result |
|---|---|---|---|---|
| `three.cfg` | 3 | 3, 1, 1 | `Claim` | no error (7,325 states) |
| `four.cfg` | 4 | 2, 1, 1 | `Claim` | no error (35,848 states) |
| `five.cfg` | 5 | 2, 1, 1 | `Claim` | no error (232,275 states) |
| `slow.cfg` (from `tight.cfg`) | 3 | 3, 2, 2 | `Claim` | no error (27,702 states) |
| `tight.cfg` | 3 | 3, 2, 2 | `Claim − 1` | `Bounded` is violated, as it must be |

The models are symmetric (`SYMMETRY Sym`), so TLC checks each ordering
once. Six models take a few minutes; they are not in the build.

### The same claim against the Go code

`TestNoStarvation` in
[`internal/sched/policy_test.go`](../internal/sched/policy_test.go) runs
`Decide` itself in 500 random worlds (2 to 6 models, random timeslice,
load and drain limits, random requests). It checks the same bound and
`Alone` every minute of simulated time.

### When you change the algorithm

Change `policy.go` and `spec/Timeslice.tla` together, rule for rule.
Then run `nix-build -A tests.tla` and `go test ./internal/sched/`.
Earlier drafts of the scheduler had starvation bugs that only TLC found.
