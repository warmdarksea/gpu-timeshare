# The scheduler: the algorithm, its bounds, and how they are checked

This document describes how gpu-timeshare decides which model is on which
GPU and which request is answered next. It gives the algorithm in plain
words, the guarantees and their worst cases as formulas of the inputs, the
code, and the TLA+ model that TLC checks.

Four files say the same thing and change together:

| What | Where |
|---|---|
| the algorithm, in English | this document, §2 |
| the algorithm, in Go | [`internal/sched/policy.go`](../internal/sched/policy.go) (all of it, one file) |
| the algorithm, in TLA+ | [`spec/Turns.tla`](../spec/Turns.tla), with [`spec/MC.tla`](../spec/MC.tla) and the `.cfg` files for TLC |
| the algorithm, in Lean 4, and proofs about it | [`proof/Timeshare/Policy.lean`](../proof/Timeshare/Policy.lean), [`proof/Timeshare/Proofs/`](../proof/Timeshare/Proofs) (§8) |

## 1. The problem and the terms

A request names a **model**, belongs to a **tenant** (the client whose
token sent it), and waits in a queue. A model must be loaded on a GPU
before it answers, and loading takes minutes. The scheduler wants few
swaps and short waits, and it must never leave a request waiting without
bound, however much anybody else has queued.

| Term | Meaning |
|---|---|
| card | One GPU. A card holds one model at a time (README: two busy models on one card each run at half speed, so sharing saves only the swap). |
| flow | One tenant's queued requests for one model. |
| load, drain | Load: start a model and wait until it answers. Drain: send it no new requests, let the ones in flight finish, then stop it. |
| turn | A card's time is cut into turns. A turn belongs to one tenant (the **owner**) and one model. Every tenant with requests for that model is answered during it, not only the owner. |
| quantum | How old a turn must be before somebody else can take the card: `max_timeslice`, or `load_ratio` × the model's load time if that is longer. |
| lost | A model is lost when it has queued requests and is on no card. |
| short | A model is short when it is on a card and has more requests queued than its cards have free slots. |
| idle | A card is idle when its model is up with nothing queued and nothing in flight. |
| the line | The tenants with queued requests, in order. The first has waited longest for a turn. |
| a tenant's line | That tenant's models with queued requests, in order. The first has waited longest for a card. |

How the lines move:

- A newcomer joins at the back: a tenant when it first has a queued
  request, a model when the tenant first queues a request for it.
- Whoever has nothing queued any more leaves.
- When a turn ends, its **tenant** goes to the back of the line.
- When a model leaves a card, it goes to the back of **every** tenant's
  line: they were all served by it.

## 2. The algorithm

### 2.1 Which model is on which card (`Decide`)

The scheduler does one *round* when something changes (a request arrives
or ends, a load finishes) and at least every 200 ms. In a round it applies
the first of these rules that has something to do, and repeats until none
has:

1. **Drained.** A draining card with nothing in flight stops. It is kept
   for the tenant and the model it drained for (rule 6).
2. **Start.** A card that drained for somebody loads their model. A free
   card goes to the first tenant that has a lost model, or failing that a
   short one. "First" means fewest cards held, then the line. The card
   loads that tenant's first lost model, else its first short one (a
   *copy*: the model is then on two cards).
3. **GiveWay.** No card is free and some model is lost: the card that has
   been idle longest stops. (An idle card does not stop for a copy. An
   idle model is warm, and a copy is only a speed-up.)
4. **IdleStop.** A card idle for `idle` stops, so the GPU can go to a
   low-power state.
5. **Pass.** A turn is a quantum old, and the tenant with the best claim
   to the card (below) wants the model that is there. The turn is now that
   tenant's, and a new quantum begins. Nothing is swapped.
6. **Drain.** A turn is a quantum old, and the tenant with the best claim
   wants another model. The old turn is over, and the card is that
   tenant's from now, for that model: it drains *for* them, and rules 1
   and 2 follow. Nobody else can have the card meanwhile, and the model
   counts as on a card already, so one claim takes one card. Any number of
   cards may drain at once.

A card that drains for a tenant, or has drained for it, counts as a card
that tenant holds, and its model as on a card. So "holds", "lost" and
"short" below see the cards as they are about to be.

**The best claim** to a card whose turn is a quantum old. A tenant with
queued requests can:

- **move**: one of its models is lost;
- **stay**: it has queued requests for the model that is on the card;
- **copy**: one of its models is short, it is not the owner, and it holds
  at least two cards fewer than the owner (so it would still hold fewer
  than the owner afterwards).

Among the tenants that can do one of these, the winner is the one with
the fewest cards, then the first in line. The owner counts one card fewer
(the card in question) and comes last among equals: it has had its turn.
The winner moves if it can, else stays, else copies.

If the winner is the owner and it stays, nothing happens. So with nobody
else to serve, a model keeps its card for as long as it has work, and its
turn is not renewed: a newcomer does not wait out a fresh quantum.

A turn that began this instant cannot be taken, whatever the quantum. It
matters only when the quantum is zero: a turn that has just passed cannot
pass again, so a round always ends (§8.2, §9).

### 2.2 Which request is answered next (`RoundRobin`)

Each model has a number of slots per card (`concurrency`). When a slot is
free on a card whose model is up:

- it goes to the tenant whose turn it is on the card (the owner), while
  that tenant holds fewer than half the card's slots and has a request to
  give: **the owner's half**;
- otherwise to the tenant with the fewest requests in flight for that model;
- among equals, to the tenant after the one served last;
- within a tenant, to its oldest request, single requests before batch
  lines (a client holds a connection open for a single request);
- never to a request whose question is already being asked (its twin
  gets the same answer).

### 2.3 Why these rules

Each rule answers a way that a simpler scheduler goes wrong.

| Simpler rule | What goes wrong | What the algorithm does |
|---|---|---|
| "Next: the model whose request has waited longest." | Two deep backlogs from yesterday alternate until both are empty; a request from today waits for all of it. The wait grows with what others have queued. | Places in line are not ages of requests. A turn's tenant goes to the back, so the wait is counted in turns. |
| Turns belong to models. | A tenant with work on seven models has seven turns for each turn of a tenant with one model. | Turns belong to tenants. A tenant's models take turns among themselves, inside its share. |
| A tenant picks its oldest flow each turn. | A flow of a tenant that is always being served on another model never comes up. | A tenant with a lost model moves to it when its turn comes, and a model that leaves a card goes to the back of every tenant's line. |
| Swap whenever a turn is over. | Two tenants on the same model would reload it for each other. | Pass: the turn changes hands, the model stays. |
| Stop an idle model for any other demand. | A warm model is evicted for a copy that only speeds another one up. | GiveWay is for lost models only. |
| A copy may take any card whose turn is old. | With three cards and two tenants, the odd card swaps every quantum. | A copy only takes a card from an owner who would still hold more afterwards. |
| Drain a card as soon as a claim exists. | With several cards, one claim drains two of them. | A card drains *for* a claim, and is that claim's from then on: the model counts as on a card, so no second card drains for it. |
| One card drains at a time (the first fix for the row above). | With several cards, an old turn waits for the drain slot behind other cards' drains: a turn can last *L* + *Q* + many × *D* (§9, entry 17). | Any number of cards drain at once, each for its own claim. |

## 3. The inputs

The bounds in §4 are formulas of these.

| Symbol | Input | Where it comes from |
|---|---|---|
| *Q* | the longest quantum | `max_timeslice`, or `load_ratio` × the slowest load |
| *L* | the longest load | bounded by `start_timeout` (default 15 min); in practice a few minutes |
| *D* | the longest drain | bounded by `request_timeout` (default 10 min); in practice one request |
| *R* | the longest request | `request_timeout` |
| *G* | cards | `gpus` |
| *T* | tenants that have queued requests at some time during the wait | the workload |
| *M* | models that have queued requests at some time during the wait | the workload |
| *k* | models that the waiting request's own tenant has queued requests for, at most at one time | the workload |
| *n* | tenants with requests for one model that is up | the workload |

A **turn** lasts at most *L* + *Q* + *D*: a load, a quantum, a drain.

Nothing else is an input. In particular the bounds do not depend on how
many requests anybody has queued, on when they were queued, or on the
order in which they arrive.

## 4. The guarantees and their worst cases

### 4.1 No starvation: the wait for a model

> A flow with queued requests has its model up on some card within
>
> **min(*T*·*k*, *T*·(*M* − 1)) turns + *D* + *L***
>
> = min(*T*·*k*, *T*·(*M* − 1)) × (*L* + *Q* + *D*) + *D* + *L*
>
> unless the flow empties first.

The *T*·*k* part is **proved in Lean for any number of cards, tenants and
models** (§8.2, `mwait_bound`): within *T*·*k* turns the flow's model is
started, or a card begins to drain for it; its own drain and load follow.
A turn there is *D* + *L* + *Q*: the drain comes first, since a card that
drains is already its next tenant's. The cap *T*·(*M* − 1) is what TLC
finds for one and two cards at small sizes (§6.5); it is not proved.

The last *D* + *L* is the flow's own drain (if its model was up and was
drained with requests still queued) and its own load.

Why, on one card. Call the flow's tenant *t* and its model *m*.

1. When the wait begins, at most *k* − 1 of *t*'s models are ahead of *m*
   in *t*'s line. A model that joins later joins behind *m*.
2. Each time *t* wins a card, it moves to its first lost model. That is a
   model ahead of *m*, or *m* itself. When that model leaves the card, it
   goes behind *m*. So *t* has at most *k* − 1 turns before the turn that
   loads *m*.
3. Between two of *t*'s turns, each other tenant has at most one: a
   tenant whose turn ends goes to the back of the line, behind *t*. A
   tenant that arrives later joins behind *t*. So at most *T* − 1 turns
   of others come before each of *t*'s.
4. That is (*T* − 1) + (*k* − 1)·*T* = *T*·*k* − 1 turns. One more turn
   can be running when the wait begins, and can be *t*'s own, on a model
   whose requests are all in flight: *T*·*k* turns.
5. It is also never more than *T*·(*M* − 1): a turn of another tenant on
   a model that is ahead of *m* in *t*'s line takes that model from ahead
   of *m* as well as *t*'s own turn would, and with *M* models there are
   only *M* − 1 others.

Special cases:

| Case | Bound |
|---|---|
| one tenant, *M* models | (*M* − 1) turns + *D* + *L*. This is the bound of the scheduler this one replaces, and it is **exact**: TLC finds a wait of exactly this length (`tight.cfg`). |
| a tenant that uses one model, among *T* tenants | *T* turns + *D* + *L*, however many models the others use. |
| everybody on one model | *D* + *L*: nothing is ever swapped. |
| *T* tenants each spread over all *M* models | *T*·(*M* − 1) turns + *D* + *L*. |

With more than one tenant the formula is an upper bound that TLC has
checked, but not always reached: §6.5 lists the longest waits TLC found
next to the formula.

The bound is per flow, and a tenant's own spread is what makes it grow
(*k*). A tenant cannot make another tenant's bound grow by queueing more
requests, or by using more models (beyond the cap *T*·(*M* − 1), which
counts models, not requests).

In numbers, with loads of 3 minutes and drains of 30 seconds:

| `max_timeslice` | turn | 3 tenants, your one model | 3 tenants, your 7 models of 8 |
|---|---|---|---|
| 2 h (the default) | 2 h 3.5 min | ≤ 6 h 14 min | ≤ 43 h 17 min |
| 15 min | 18.5 min | ≤ 59 min | ≤ 6 h 32 min |
| 5 min (quantum 12 min: `load_ratio` 4) | 15.5 min | ≤ 50 min | ≤ 5 h 29 min |

These are worst cases: every other tenant has work for a model of its own
for the whole time, and every load and drain takes its limit. They are
what `max_timeslice` buys and costs; §4.3 is the other side.

### 4.2 No starvation: the wait for a slot

Once the model is up, a request waits for a slot.

> A tenant with a queued request for a model that is up, and none in
> flight, gets one of the next *n* + *h* slots that come free on that
> model's cards (*n* the tenants with requests for it, *h* half a card's
> slots), or the model drains first (and §4.1 applies again).

A free slot goes to the owner of the turn while it holds fewer than half
the card's slots (at most *h* slots), and otherwise to the tenant with
the fewest requests in flight. A tenant with none in flight is ahead of
every tenant with one, and among tenants with none the order is
round-robin, so at most *n* − 1 others are served first. A slot comes free
within *R*. The rule for each slot is proved (§8.2, `step_owner`,
`step_fewest`, `step_waiting`); the count *n* + *h* is read off it.

A request that is not its tenant's oldest waits for its tenant's older
requests too. That is the tenant's own queue, and no bound on it is
possible or wanted.

### 4.3 Few swaps

> A model is taken off a card only when the card is idle, when the turn
> is at least a quantum old, or when its server fails.

So between two swaps on one card there is at least a quantum of the
model being up with work, or there is no work for it at all. Under any
workload, the part of a card's time that goes to swapping is at most

> (*L* + *D*) / (*Q* + *L* + *D*)

For *L* = 3 min and *D* = 30 s: 3% at the default 2 h, 19% at 15 min.
`load_ratio` (default 4) keeps *Q* ≥ 4·*L* for a slow model whatever
`max_timeslice` says, which caps the fraction near 20%.

Swaps that are never made:

- one tenant with one model, or any number of tenants on one model: none
  (`TestNoSwapWithoutNeed`);
- tenants that share a model have consecutive turns on it and pay one
  swap for all of them (`TestTenantsShareEvenly`);
- cards that are split evenly stay as they are: a copy does not take a
  card it would have to give back (`TestCardsShareEvenly`).

### 4.4 Latency and fairness, defined

**Latency** is how long until your work begins to be done. Two of them:

- *Flow latency*: from when tenant *t* has a request queued for model *m*
  until one of those requests is being answered.
- *Tenant latency*: from when *t* has requests queued and none being
  answered until any one of them is.

Each is two waits: for the model to be up, and then for a slot.

| | until the model is up | then, until a slot |
|---|---|---|
| a flow | *T*·*k* turns + *D* + *L* (§4.1; proved) | one of the next *n* + *h* slots that come free (§4.2; proved) |
| a tenant | ***T* turns** + *D* + *L* (proved) | the same |

A turn is at most *D* + *L* + *Q*; *n* is the tenants with requests for
the model and *h* half a card's slots. The tenant's bound has no *k* and
no number of models in it: turns belong to tenants, so with *T* tenants
somebody's job of yours is on its way within *T* turns, however many
models there are. The wait for a slot has no quantum in it: on a model
that is up, a request waits for single requests to end, never for a turn.

**Fairness** is three statements, each stronger than the last:

1. *Nobody is overtaken twice round.* While you hold no card, every turn
   that begins goes to you or to a tenant that stood before you in the
   line and held none either; so fewer than *T* turns begin before yours
   (proved, in turns and in time).
2. *Spreading and queueing buy nothing.* Turns are a tenant's, not a
   model's or a request's: a tenant with work on four models and a tenant
   with work on one have the same number of turns, and so do a tenant
   with ten requests and one with ten thousand (tested:
   `TestSpreadingBuysNothing`, `TestTenantsShareEvenly`; the proofs above
   never count models or requests of *other* tenants).
3. *A share of the card.* During its own turn a tenant with requests to
   give holds at least half the card's slots (**the owner's half**,
   proved for each free slot); and the cards are divided between the
   tenants that have work for them to within one card (tested:
   `TestCardsShareEvenly`). With equal turns, that is at least about
   1/(2·*T*) of the card's time for each tenant with work, less the
   swaps. That last figure is arithmetic on the two statements before
   it; it is not itself a theorem.

What is *not* claimed: equal GPU-seconds. A tenant is also answered
during other tenants' turns on a model it shares (it "rides"), and that
is deliberate: it needs no swap, and it is what keeps latency on a model
that is up down to single requests. The owner's half is the limit on it.
Before that rule there was none (§9, entry 18).

### 4.5 No waste, and rounds end

- Once a round has settled, no card is free while a model is lost or
  short, and no card is idle while a model is lost.
- A round makes at most 3·*G* decisions: each card at most drains, stops
  and starts. The rules cannot loop.
- The scheduler never stops a card that has requests in flight. Only a
  failing server loses requests, and those are retried.

### 4.6 What can still go wrong

- **A request that never ends.** Every bound needs *D* and *R* to be
  finite. `request_timeout` makes them so.
- **A model that does not load.** A failed load ends the turn like any
  other (the tenant goes to the back), so it cannot hold the line. After
  two failures the model's requests are refused for `broken_for`. The
  bounds are for a model that loads when it is asked to.
- **A restart.** The lines are in memory. After a restart they are
  rebuilt from the queue, oldest request first. That costs at most one
  round of the line's order.
- **Many tenants.** The wait is *T* turns even for one small request. It
  is the price of equal turns, and `max_timeslice` is the knob.
- **A tenant with many tokens** is many tenants.

## 5. The code

[`internal/sched/policy.go`](../internal/sched/policy.go) is the whole
algorithm: its header is §2 again, and each rule in `rule()` carries its
name in brackets.

| In this document | In `policy.go` |
|---|---|
| a round | `Decide(cards, flows, slots, lines, now, pol)`: pure. It returns the actions and the lines as they are afterwards. |
| rules 1 to 6 | `(*world).rule()`, tried in that order. A rule that applies changes `world` (Decide's copy), and the next sees the change. |
| the best claim | `(*world).winner(card)` |
| who gets a free card | `(*world).claim()` |
| the lines | `Lines`; `join` (newcomers, leavers), `Ended` (a turn's end) |
| lost, short, idle | `lost`, `short`, `longestIdle` |
| quantum | `Policy.quantum(card)` |
| §2.2 | `RoundRobin` |

[`internal/sched/driver.go`](../internal/sched/driver.go) applies the
actions and holds what `Decide` needs between rounds: one `card` per GPU
(what is on it, whose turn, since when) and the `Lines`. It ends a turn
itself in one case, a load that fails or a server that dies, and calls
`Lines.Ended` for it as `Decide` does for the turns it ends.

## 6. The TLA+ model

[`spec/Turns.tla`](../spec/Turns.tla) is §2.1 in TLA+. TLC, the TLA+
model checker, examines every reachable state of it for small numbers of
tenants, models and cards, and checks five invariants in each.

### 6.1 How the model relates to the code

| TLA+ | Go | Note |
|---|---|---|
| `st[c]`, `on[c]`, `owner[c]` | `Card.State`, `.Model`, `.Owner` | |
| `next[c]` | `Card.Next` | The model the card drains for, or has drained for; `owner[c]` is then the tenant it is for. |
| `clock[c]` | `now - Card.TurnAt` | Also times a load and a drain. |

| `busy[c]` | `Card.Inflight > 0` | Only "something is in flight". |
| `q[t][m]` | `Flow.Queued > 0` | Only "the flow has queued requests". The number changes no decision but *short*. |
| `more[m]` | queued > free slots | The adversary says when a model is short. |
| `line`, `mline[t]` | `Lines.Tenants`, `Lines.Models[t]` | |
| `Drained`, `Start`, `GiveWay`, `Pass`, `Drain` | rules 1, 2, 3, 5, 6 | The scheduler: `Decide` in the spec. |
| `Winner`, `Pick`, `Rank` | `winner` | |
| `NextClaim`, `StartPick` | `claim` | |
| `Ended` | `Lines.Ended` | |
| `IdleStop` | rule 4 | In the spec the world does it, at any time a card is idle: every value of `idle` at once. |
| `Loaded`, `Fail`, `Arrive`, `Taken`, `Work`, `Finish`, `Flip` | the model servers, the clients | Not the scheduler: TLC tries every order. |
| `Tick` | time | |
| `MaxTimeslice`, `MaxLoad`, `MaxDrain` | *Q*, *L*, *D* | |

### 6.2 What the model assumes

- **Time is discrete.** `Tick` adds one unit to every clock.
- **The scheduler takes no time.** `Tick` is not possible while a
  scheduler action is (`~ENABLED Decide`). The code does the same: a round
  applies every rule that applies before time goes on.
- **Everything else is an adversary.** Requests arrive for any flow at
  any time. A flow's queue empties at any time its model is up, or never.
  A load takes any time up to `MaxLoad`, or fails. Requests in flight take
  any time up to `MaxDrain`. A model is short whenever the adversary says
  so. An idle card stops whenever the adversary says so. `Overdue` holds
  time back at the two limits.
- **Rules are tried in any order** where the code has a fixed one, except
  where a guard says otherwise (`Drain` needs no free card and no possible
  `Pass`). Which idle card gives way, and which of several old turns is
  examined first, are free in the spec and fixed in the code (the longest
  idle; the owner with the most cards). So the invariants hold for more
  schedulers than the one in Go.
- **One flow is watched.** `watched` is any one flow, chosen in `Init`.
  `wait` counts the ticks in which it has queued requests and its model
  is not up on any card. It goes to 0 when its model finishes loading, and
  when its queue empties. `Init` tries every flow, and the tenants, models
  and cards are interchangeable (`SYMMETRY`), so the invariant holds for
  all of them.
- **The watched model does not fail** (`Fail` is for the others). §4.6.

### 6.3 What the model does not include

- §2.2, the requests within a model. It does not change which model is on
  which card. §4.2 is argued above and `RoundRobin` has unit tests.
- `load_ratio`: one `MaxTimeslice` stands for the longest quantum.
- The counts of requests, and how long each takes.
- Fair shares (§4.4), which are statements about long runs.
- Liveness as a temporal formula. `Bounded` is stronger than "eventually":
  it is an invariant with a number in it, so TLC needs no fairness
  assumption and its symmetry reduction stays sound.

### 6.4 The invariants

| Invariant | Says | § |
|---|---|---|
| `Lines` | The line is exactly the tenants with queued requests, each once; the same for each tenant's line. | 1 |
| `NoKill` | A card that is down has nothing in flight: no rule stops a card that is answering. | 4.5 |
| `NoWaste` | When no rule applies, no card is free while a model is lost or short, and none is idle while a model is lost. | 4.5 |
| `Settles` | At most 3·*G* scheduler actions happen with nothing else between them. | 4.5 |
| `Bounded` | `wait <= MaxWait`, with `MaxWait` the formula of §4.1. | 4.1 |

The formula, in [`spec/MC.tla`](../spec/MC.tla):

```tla
Turn1 == MaxLoad + MaxTimeslice + MaxDrain
Turns == IF T * K < T * (M - 1) THEN T * K ELSE T * (M - 1)
Claim == Turns * Turn1 + MaxDrain + MaxLoad
Tight == Claim - 1      \* where the claim is exact, TLC must find a violation of this
```

`K` limits how many models the watched flow's tenant has queued requests
for at one time (`ACTION_CONSTRAINT Narrow`). With `K` = *M* there is no
limit.

### 6.5 The checks

`nix-build -A tests.tla` runs TLC on these. All five invariants are
checked in each.

| Config | Tenants | Models | Cards | `K` | *Q*, *L*, *D* | `MaxWait` | Result |
|---|---|---|---|---|---|---|---|
| `t3m1.cfg` | 3 | 1 | 1 | 1 | 2, 2, 1 | `Claim` (3) | no error (468 states) |
| `t1m3.cfg` | 1 | 3 | 1 | 3 | 3, 1, 2 | `Claim` (15) | no error (20,816 states) |
| `t2m2.cfg` | 2 | 2 | 1 | 2 | 2, 2, 2 | `Claim` (16) | no error (29,836 states) |
| `t3m2.cfg` | 3 | 2 | 1 | 2 | 2, 1, 1 | `Claim` (14) | no error (167,952 states) |
| `t2m3.cfg` | 2 | 3 | 1 | 3 | 2, 1, 1 | `Claim` (18) | no error (589,208 states) |
| `one.cfg` | 2 | 3 | 1 | 1 | 2, 1, 1 | `Claim` (10) | no error (49,240 states) |
| `g2.cfg` | 2 | 2 | 2 | 2 | 2, 1, 1 | `Claim` (10) | no error (491,166 states) |
| `tight.cfg` | 1 | 3 | 1 | 3 | 3, 1, 2 | `Claim − 1` (14) | `Bounded` is violated, as it must be |

The whole set takes under a minute. Two larger configurations are not in
the build: `big.cfg` (3 tenants, 3 models, `K` = 1; several minutes) and
two cards with three models. Their runs at the final formula had not
finished when this was written; run them before relying on those sizes.

(The state counts are for the algorithm as it is now. The table of longest
waits below was measured before drains were reserved, §9 entry 17, and has
not been measured again; the bound itself still holds in every
configuration.)

The longest wait TLC can reach, found by lowering `MaxWait` until
`Bounded` breaks, next to the formula:

| Tenants | Models | Cards | `K` | *Q*, *L*, *D* | longest wait TLC finds | formula |
|---|---|---|---|---|---|---|
| 1 | 3 | 1 | 3 | 3, 1, 2 | 15 | 15 |
| 2 | 2 | 1 | 2 | 3, 1, 2 | 13 | 15 |
| 3 | 2 | 1 | 2 | 3, 1, 2 | 17 | 21 |
| 2 | 3 | 1 | 3 | 3, 1, 2 | 25 | 27 |
| 2 | 3 | 1 | 1 | 3, 1, 2 | 12 | 15 |
| 2 | 3 | 1 | 2 | 2, 1, 1 | 15 | 18 |
| 1 | 2 | 2 | 2 | 3, 1, 2 | 7 | 9 |
| 2 | 2 | 2 | 2 | 3, 1, 2 | 9 | 15 |
| 3 | 2 | 2 | 2 | 2, 1, 1 | 9 | 14 |
| 2 | 3 | 2 | 1 | 2, 1, 1 | 6 | 10 |

The formula is exact for one tenant. With two or three tenants on one
card, TLC's longest wait is 2 to 4 ticks short of it in these
configurations (a drain or two, or a drain and a load): the argument of
§4.1 counts a whole turn where the turn that is running when the wait
begins has no load left, or where the tenant's own drain and a turn's
drain are the same drain. With two cards the waits are shorter still, as
they should be, and the formula for one card is claimed for any number.

What these checks are not: a proof for all sizes. TLC covers up to three
tenants, three models and two cards, with small times. §4.1's argument is
what says the pattern continues, and `TestNoStarvation` (§7) samples
larger sizes.

### 6.6 Running TLC by hand

```
cd spec
JAVA_TOOL_OPTIONS=-Xmx4g tlc -workers auto -config t2m3.cfg -metadir /some/disk/dir MC.tla
```

TLC's JVM takes a quarter of the machine's memory unless told otherwise,
and writes its states under `-metadir`. Run a few at a time, and not into
a tmpfs. `big.cfg` (three tenants, three models) takes several minutes.

## 7. The same claims against the Go code

[`internal/sched/policy_test.go`](../internal/sched/policy_test.go) has a
simulated machine, `sim`, that runs `Decide` itself a minute at a time.
On every decision it checks what the spec's invariants say: no card with
requests in flight is stopped, no turn is taken before its quantum, a
round is at most 3·*G* decisions and settles, and `NoWaste`.

- `TestNoStarvation`: 200 random worlds (1 to 4 tenants, 1 to 5 models, 1
  to 3 cards, random limits, each tenant using a random number of the
  models). Requests arrive and are taken at random; loads and drains take
  up to their limits. Every flow's wait stays within §4.1's formula, with
  that tenant's own *k*.
- `TestTenantsShareEvenly`, `TestSpreadingBuysNothing`,
  `TestNoSwapWithoutNeed`, `TestCardsShareEvenly`: §4.3 and §4.4, with
  every flow kept full.
- `TestStart`, `TestTurn`, `TestPass`, `TestOwnModelsTakeTurns`,
  `TestIdle`, `TestLoadRatio`, `TestCards`, `TestPure`: one rule each.

The end-to-end tests (`cmd/gpu-timeshare/e2e_test.go`) run the real
driver against stub model servers: `TestTurns` (a long batch gives way to
another tenant's model after `max_timeslice`) and `TestTwoCards` (a copy
on the second card, each told its GPU; an idle copy gives way).

## 8. The Lean model and its proofs

TLC checks every state of a few small sizes. A proof assistant checks a
claim for every size at once, and the price is that the proof has to be
written. [`proof/`](../proof) is the algorithm a third time, in Lean 4,
with proofs about it. They hold for any number of tenants, models and
cards: the three are type parameters.

### 8.1 The model is the code, checked

[`proof/Timeshare/Policy.lean`](../proof/Timeshare/Policy.lean) is
`policy.go`'s `Decide` again, function for function: `decide`, `rule`,
`winner`, `claim`, `Lines.join`, `Lines.ended` and the rest, with the same
names. It is not an abstraction like the TLA+ model. It takes the same
arguments (cards with their counts and times, flows, slots, lines, the
time, the policy) and returns the same actions and lines. (One field of
a card is the model's alone: `since`, when the card began to load or to
drain. No rule reads it; the proofs about time do.)

It is executable, and that is how it is tied to the Go code:

- `TestCases` (`internal/sched/cases_test.go`) runs 300 simulated worlds
  of up to 4 tenants, 5 models and 4 cards, and writes every round to a
  file: what `Decide` was given, and what it answered.
- `timeshare-check` ([`proof/Check.lean`](../proof/Check.lean)) runs the
  Lean `decide` on every round in the file and fails if any answer
  differs, action for action and line for line.
- `nix-build -A tests.lean` does both: 90,000 rounds, 44,630 decisions, no
  difference.

The check has teeth: with the owner's rank, the copy rule or `toBack`
changed in the Lean model, it reports hundreds to thousands of
differences. (One change it cannot see is the "no card is free" guard of
GiveWay. With a free card and a lost model, Start always fires first, so
the guard is redundant. It stays, for the reader.)

This is a test, not a proof that the two agree. A change to `policy.go`
that the simulated worlds never exercise would pass.

### 8.2 What is proved

All of it is for any number of tenants and models (they are type
parameters), and every theorem is about `rule`, `run` and `decide` as
defined in `Policy.lean`.

**About one rule and one round, for any number of cards and any world**
(no assumption that the world is reachable):

| Theorem | Says | File |
|---|---|---|
| `rule_step`, `rule_effect` | A rule changes exactly one card, in one of five ways, each with its reason and its effect on the lines. | `Proofs/Step.lean`, `Effect.lean` |
| `rule_noKill` | **NoKill.** A card that is down after a rule was down before it, or had nothing in flight. | `Proofs/Step.lean` |
| `rule_thrift` | **No turn is cut short.** A card that is up before a rule and not after it was idle, or its turn was a quantum old. This is §4.3's premise. | `Proofs/Step.lean` |
| `rule_pass_old` | A turn changes hands without a swap only when it is a quantum old. | `Proofs/Step.lean` |
| `round_settles`, `run_length` | **A round ends**, within 3·*G* decisions: `decide`'s fuel is never what stops it. | `Proofs/Settles.lean` |
| `join_nodup`, `mem_join_tenants`, `mem_join_models` | **Lines.** After `join`, the line is exactly the tenants with queued requests, each once, and the same for each tenant's line. | `Proofs/Lines.lean` |
| `before_join_tenants`, `before_join_models`, `before_toBack` | Newcomers join behind: `join` puts nobody before somebody who was there, and going to the back takes one from before the others and nobody else. | `Proofs/Lines.lean` |

**No waste, on any number of cards** (`Proofs/NoWaste.lean`).

> **`settled`.** When no rule applies: no draining card has finished; no
> card that drained for somebody waits to be started; no card is free
> while a model is lost or short; no card is free or idle while a model
> is lost; no card has been idle for `idle`; and no turn can be taken:
> wherever a turn is old enough to have a winner, the winner is the owner,
> staying.

That is `NoWaste` of §4.5 and more, for every world (reachable or not).
The scheduler never holds a card back and never waits to do what it could
do now.

**No starvation, on any number of cards, counted in turns**
(`Proofs/Winner.lean`, `Multi.lean`, `MultiRule.lean`, `MultiBound.lean`).
The system is the cards and the lines (`MSys`); a history (`MTrace`) is
rounds of `decide` over all the cards and, between them, whatever the
model servers do, each on its own card (requests come and go, a load
finishes, a load fails, a server dies at work or while it drains).

A turn *begins* when a free card is started on, when a turn passes from
one tenant to another, and when a card begins to drain for somebody (the
start that follows that drain is not a new turn).

> **`mturns_bound`.** Take a tenant *t* with requests queued for a model
> *m*. In any history in which that flow stays queued, *m* is not started
> and no card drains for it, at most ***K*·*N* − 1 charged turns** begin.
> A turn is charged if it begins while *t* holds no card (whoever it goes
> to), or if it is *t*'s own.

Why: while *t* holds no card, every card the scheduler hands out, on a
free card, by passing a turn, or by draining for somebody, goes to *t* or
to a tenant that stood before *t* in the line and held no card either
(`winner_first`, and the same for `claim`). There are fewer than *N* of
those, and once one of them holds a card it is not one of them again:
when its turn ends it goes behind *t*. And each turn of *t*'s own is for
its first lost model, which is *m* or stood before *m* in its line; there
are fewer than *K* of those, and a model that leaves a card goes behind
*m*. The measure is `mPot` (`Proofs/Multi.lean`); `mpot_ended`,
`mpot_start`, `mpot_pass` and `mpot_congr` say what each kind of change
to one card does to it, and a drain is an end and a start at once.

**No starvation, on any number of cards, in time** (`Proofs/MultiTimed.lean`,
`MultiLast.lean`, `MultiWait.lean`). Time is in ticks, and it moves only
from a state in which a round would decide nothing, as in the TLA+ model
(the scheduler has its say at every instant). A load takes at most *L*
ticks, or fails; requests in flight on a draining card end within *D*.

> **`mwait_bound`.** While tenant *t* has requests queued for model *m*,
> and until *m* is started or a card begins to drain for it, at most
> ***K*·*N*·(*D* + *L* + *Q*) ticks** go by -- on any number of cards,
> for any number of tenants and models, whatever else is queued and
> whatever the model servers do within their limits. *Q* is the longest
> quantum (`max_timeslice`, or `load_ratio` × *L*) and at least one tick,
> so a quantum of zero is covered.

The proof is a budget that no step exceeds (`Bud`, `step_inv`): the time
now, plus the measure `mPot` times the longest turn, plus the time left
on a card -- on each of *t*'s cards while it holds one, on some card
while it holds none. Then:

- a turn that begins while *t* holds no card, or is *t*'s own, lowers the
  measure (`rule_multi`), and so does the turn that takes *t*'s last card
  (`rule_last`: whoever takes it ranked below an owner with one card, so
  it held none, and it stands before *t* now, who went to the back);
- a tick lowers the time left by one, and there is always some left:
  when the scheduler would decide nothing, every turn old enough to be
  taken has its owner as the winner, staying (`settled`); but *t* has a
  lost model, so on its own card it would move (`winner_lost`), and on
  anybody's card while it holds none it or somebody of rank 0 before it
  would win, which the owner is not (`winner_first`).

This is the theorem the reserved drains were for (§9, entry 17): with one
drain at a time it was false.

**Tenant latency, and nobody overtaken twice round** (`tenant_wait_bound`
in `Proofs/MultiWait.lean`, `tenant_turns_bound` in `MultiBound.lean`).
For the flow that is first in its tenant's line -- the one of its flows
that has waited longest:

> fewer than *N* charged turns begin before its own, and at most
> ***N*·(*D* + *L* + *Q*) ticks** go by before its model is started or a
> card begins to drain for it.

One turn for each tenant with queued requests, however many models there
are: §4.4's tenant latency, and its first statement of fairness.

**The slots of a model that is up** (`Proofs/Slots.lean`). `roundRobin` in
`Policy.lean` is `RoundRobin` in `policy.go`, checked against it on 20,000
random calls (§8.1). For each free slot (`Picking.step`):

| Theorem | Says |
|---|---|
| `step_owner` | **The owner's half.** While the tenant whose turn it is has a request to give and holds fewer than half the card's slots, the slot is its. |
| `step_fewest` | Otherwise the slot goes to a tenant with a request to give and no more in flight than anybody else who has one. |
| `step_waiting` | So a tenant with a request to give and none in flight is not passed over, the owner's half aside, for anybody who has one in flight. |

**The last step** (`Proofs/MultiUp.lean`).

> **`up_bound`.** Once a card has a model coming -- it drains for it, has
> drained for it, or is loading it -- the model is up within ***D* + *L***
> ticks, unless its load fails. No rule takes such a card for anything
> else (`rule_coming`).

Together: a flow with queued requests has its model up within
*K*·*N*·(*D* + *L* + *Q*) + *D* + *L* ticks, on any number of cards, if
its load does not fail. That is §4.1's formula with *T*·*k* turns.


The build fails on an unfinished proof (`assert_no_sorry`), and
`tests.lean` fails if a module of `proof/` was not checked.

### 8.3 What is not proved yet

**1. The cap *T*·(*M* − 1)** of §4.1. *T*·*k* is proved; the cap is TLC's
finding at small sizes.

**2. Shares of the card over time** (§4.4, third statement). What is
proved is the owner's half, slot by slot. That turns are equal in number
over a long run, that cards are divided to within one, and the figure
1/(2·*T*) that follows from them are tested or argued, not proved. (The
Lean `roundRobin` is the one that runs, as `decide` is: §11.)

**3. That the Lean model and the Go code agree.** That is a test (§8.1).
It does not need to be true for the program to be right: the Lean model
decides (§11), and what is unproved there is the text interface around
it. The test keeps `policy.go` an honest page to read.


(An earlier proof for one card, `wait_bound`, was about the rule before
drains were reserved, §9 entry 17, and went out with it; `mwait_bound`
covers one card as it does any number.)

### 8.4 Running it

```
nix-build -A proof          # type-checks the model and every proof
nix-build -A tests.lean     # and the model against the Go code
```

Mathlib comes from nixpkgs (`leanPackages.mathlib`), about 1.6 GB the
first time; lake fetches nothing. `Timeshare/Policy.lean` imports nothing,
because nixpkgs' Mathlib has no objects to link an executable against;
the proofs import Mathlib and are only type-checked.

## 9. The bug log

Every defect found in this scheduler, by whatever means, in the order it
was found. Each entry says what the repository was at the time, what was
wrong, how it showed, and what the fix was. Add to it; do not tidy it.

About the states: everything up to entry 16 happened in one uncommitted
working tree on top of commit `4373e4a` (the per-model scheduler:
`policy.go`'s `Decide` over `[]Model`, `card.go`, `spec/Timeslice.tla`).
That tree was committed as `6a4b5df` on branch `tenant-turns`. So for
those entries there is no commit to check out; the draft is described.
From entry 17 on, entries name commits.

### 9.1 Found by reading, before any code

**1. "Oldest request first" makes the wait grow with other tenants'
backlogs.** *State:* `4373e4a`; the proposal on the table was: give each
model a timeslice, and when it ends, swap to the model whose request has
waited longest. *Defect:* that is first-come-first-served over backlogs.
Models A and B each hold 10,000 requests from t = 0; a request for C
arrives at t = 1. A and B alternate until every request older than C's is
answered. C is not starved, but its wait is the whole backlog, not a
number of turns. *How found:* working the example by hand. *Fix:* a place
in line is not the age of a request. Whoever has had a turn goes to the
back, and newcomers join at the back (§1).

**2. Turns per model let a tenant take more by spreading out.** *State:*
`4373e4a`, the code as it ran: `Decide` gave the card to the waiting
model that loaded longest ago. *Defect:* a tenant with work on seven
models had seven turns for each turn of a tenant with one; an interactive
tenant waited seven timeslices behind one batch. *How found:* by hand,
from the classify pipeline's seven models. *Fix:* turns belong to
tenants (§2.1).

**3. The first tenant-fair proposal starved flows.** *State:* `4373e4a`
plus `tmp/scheduling_plan1.md` in the parent repository (virtual time per
tenant; swap when the tenant furthest behind has no work on the loaded
model and everybody being served is Δ ahead of it). *Defect:* a tenant
being served on the loaded model is never the one furthest behind, so its
requests for *another* model are never the reason for a swap. Tenants are
not starved; flows are. *How found:* by reading the swap rule against a
tenant with two models. *Fix:* that design was dropped; each tenant keeps
a line of its own models (§1), and a tenant with a lost model moves to it
when its turn comes.

### 9.2 Found by TLC

For these the state was: `spec/Turns.tla` existed as a draft and
`policy.go` had not been rewritten yet (entries 4 to 7), or had (entry 8).
The configurations are the constants TLC ran with: tenants, models, cards,
then `MaxTimeslice`, `MaxLoad`, `MaxDrain`.

**4. A model that was being served stayed first in its tenant's line.**
*Draft:* `Start` moved the tenant and its model to the back when the turn
*began*; `Pick` was the first model in the tenant's line among the one on
the card and those on no card. *Config:* 2 tenants, 2 models, 1 card; 2,
1, 1. *Trace:* t1 queues b; b starts (the line is `<<b>>`, so moving b to
the back does nothing); t1 queues a, which joins behind b: `<<b, a>>`.
When the turn is old, t1's first pick is b, which is on the card: stay.
For ever. `Bounded` is violated with `wait` growing without limit while
only t1 is active. *Fix (first attempt):* the owner moves if it can.
Entry 6 replaced it.

**5. Riders kept their order.** *Draft:* as entry 4 with its fix; a model
went to the back only in the line of the tenant whose turn it was.
*Config:* 2 tenants, 3 models, 1 card; 2, 1, 1. *Trace:* t1 has
`<<b, c, a>>`. t1's turn on b; t2's turn on c, during which t1's requests
for c are answered too, but c stays second in t1's line; t1's next turn
picks b again (first lost), then c, and a waits past the bound of that
day, (*T*·*M* − 1) turns. *Fix:* a model that leaves a card goes to the
back of every tenant's line, and nothing moves when a turn begins
(`Ended` in the spec, `Lines.Ended` in Go).

**6. Two tenants passed a card between them for ever.** *Draft:* with
entry 5's fix; `Pick` for a tenant that is not the owner still preferred
the model on the card when it stood earlier in its line. *Config:* 2
tenants, 2 models, 1 card; 2, 2, 2. *Trace:* t1 and t2 both queue b, t1
also a; t1's line is `<<b, a>>`. The turn passes t1 → t2 → t1 → ...: each
time the winner is the one who is not the owner, and its pick is b. Model
a is never loaded. *Fix:* a tenant moves if it can: `Pick` is its first
lost model, and only if it has none the model on the card.

**7. Two cards drained for one claim.** *Draft:* with entry 6's fix;
`Drain` was allowed whenever no card was draining. *Config:* 2 tenants, 2
models, 2 cards; 2, 1, 1. *Trace:* card c1 drains and is stopped
(`Drained`); before `Start` puts the claimant's model on it, `Drain` fires
on c2 for the same claim, since no card is draining at that moment.
`Settles` (a round is at most 4 decisions, as it then was) is violated.
*Fix:* `Drain` also needs every card to be in use. In Go, `[Start]` is
tried before `[Drain]`, and the guard is there as well.

**8. The bound was wrong by a turn.** *State:* the Go rewrite existed and
`TestNoStarvation` passed with the formula min(*T*·*k* − 1, *T*·(*M* − 1))
turns. *Config:* 2 tenants, 3 models, 1 card, the watched tenant limited
to one queued model (`K` = 1); 3, 1, 2. *Trace:* t1 owns the card with
m2, all of whose requests are in flight (nothing queued); t1 queues m1;
t2 queues m3. t1's turn runs out (3), drains (2), t2's turn (1 + 3 + 2),
m1 loads (1): 12 ticks, and the formula said 9. *Defect:* the argument
forgot the turn that is running when the wait begins, which can be the
waiting tenant's own. *Fix:* the formula, to *T*·*k*; the algorithm was
right. The random simulation had not found it in 200 worlds.

**9. (Not a defect.) A copy drained a card where a pass would have
done.** *Config:* 2 tenants, 2 models, 2 cards. *Trace:* t1 holds both
cards (a and b); a is short; t2 has requests for a. On b's old turn t2
wins with a copy of a, so b drains for a second a, and then t1's b, now on
no card, takes the first card from a: two swaps where passing the turn on
the first card to t2 would have needed none. *Change:* `Drain` waits
while any `Pass` is possible.

### 9.3 Found by the Go tests

**10. The simulator invented a request in flight.** *State:* first run of
the new `policy_test.go`. *Symptom:* `TestNoStarvation`: "stops a card
with 1 in flight". *Defect:* in the test, not the scheduler: `sim` set
`Inflight = 1` on every `Drain`, but `Decide` drains and stops a card
with nothing in flight in one round. *Fix:* the simulator leaves
`Inflight` alone.

**11. The log named a card nobody had configured.** *State:* the driver
rewritten for several cards. *Symptom:* the end-to-end test
`TestIdleUnloadKillsTheGroup` looked for "b: idle for" and found
"b on card0: idle for". *Fix:* with one card the log names only the model
(`Scheduler.on`).

**12. "Its turn is 0s old."** *State:* `TestTurns` just written, with
`max_timeslice = "400ms"`. *Symptom:* the drain line in the log said the
turn was 0s old. *Defect:* the age was rounded to a second. *Fix:* rounded
to 100 ms.

### 9.4 Found with the Lean model

**13. (Not a defect.) GiveWay's "no card is free" guard is redundant.**
*State:* `proof/Timeshare/Policy.lean` just written and agreeing with Go
on 90,000 rounds. *How found:* changing the model to see whether the
differential test would notice; dropping that guard changed nothing.
With a free card and a lost model, `[Start]` always fires first. The
guard stays, for the reader.

**14. A timeslice of zero made a round endless.** *State:* the Lean model
agreed with Go; the proof that a round ends (`Proofs/Settles.lean`) was
being written. *Defect:* with `max_timeslice = "0"` and two tenants with
requests for one model, `[Pass]` gave the turn to the other tenant with a
turn age of zero, which was at once old enough to pass back. Go's
`Decide` loops `for { rule() }` and never returned; the driver calls it
with its mutex held, so the whole scheduler would have hung. *How found:*
the proof needs every rule to move a card down a ladder, and there was no
step down for a pass. Reproduced in Go as `TestZeroTimeslice` (it timed
out). TLC could not see it: in the spec a new turn's clock is 0 and
`MaxTimeslice` was at least 1 in every configuration. *Fix:* a turn that
began this instant cannot be taken (`winner` in Go and Lean:
`age < quantum || age <= 0`); the spec states `ASSUME MaxTimeslice >= 1`.

**15. A server that died while draining sent its tenant to the back
twice.** *State:* `turns_bound` being set up; `Env` (what a model server
may do between rounds) being written. *Defect:* `Decide` ends a turn when
the card begins to drain (`Lines.Ended`); if the server then died, the
driver's `failed` called `Lines.Ended` again, moving the tenant behind
whoever had joined in between. One place in line, once per such death.
*How found:* the measure of §8.2 could not be shown to hold through that
step. *Fix:* `failed` ends a turn only if the card was not draining.

**16. (Process.) Eleven model checkers at once.** *State:* the survey of
longest waits (§6.5). *Symptom:* the session was killed for memory.
*Cause:* TLC's JVM takes a quarter of the machine each by default, and
its state files were going to a tmpfs. *Fix:* `JAVA_TOOL_OPTIONS=-Xmx4g`,
a few at a time, `-metadir` on disk (§6.6).

### 9.5 After `6a4b5df`

**17. One drain at a time made a turn on several cards wait for the drain
slot.** *State:* `fae0a85` (the algorithm of `6a4b5df`; `wait_bound`
proved for one card, `mturns_bound` and `settled` for any number).
*Defect:* a design one. Rule 6 let one card drain at a time (entry 7's
fix), and chose "from the owner with the most cards, the oldest turn
first". On several cards, a tenant holding a card on one model while
another of its models waited had to wait for its own old card to get the
drain slot, behind every old card of an owner with more cards. By hand,
about 2·*G* + *N* drains could come first, each up to *D*; so a turn was
not *L* + *Q* + *D* but *L* + *Q* + (a polynomial in cards and tenants)
× *D*, and §4.1's formula, which the doc claimed for any number of cards,
was not true of several. *How found:* trying to prove a bound in time for
several cards: `settled` showed that such a tenant's old card implies a
drain in progress somewhere, and nothing bounded how many. TLC's two-card
configurations had *D* of 1 or 2 and could not show it; the random
simulation did not either. *Fix* (`7a5e695`): a card drains

*for* the claim that took it. `Card.Next` (Go), `next` (spec and Lean) is
the model it will load; its owner is the new tenant from the moment it
begins to drain; `held` and `placed` count such a card as that tenant's
and that model's. `[Drained]` keeps the reservation, `[Start]` honours it
before anything else, and the "no card is draining" guards on `[Pass]` and
`[Drain]` are gone. In the driver a server that dies while draining leaves
the card to whom it was to go. The cost: a free card is no longer always
the best claim's (a card that has drained goes to whom it drained for,
even if a tenant with fewer cards has arrived since), and a model is
loaded for a claim even if that claim's requests went away during the
drain.


**18. A tenant could take half of everybody else's turns.** *State:*
`452e570` (reserved drains, `mwait_bound` and the `lean` build done; free
slots went to the tenant with the fewest requests in flight, whoever's
turn it was). *Defect:* a design one, found by asking what "a fair share"
should mean. Alice has work on models A and B, Bob on A only, one card.
Bob's turn loads A, where Alice has requests too and gets half the slots;
Alice's turn always goes to B (a tenant moves to a model of its own that
is on no card), where she is alone. Turns are equal, and Alice has about
three quarters of the card: a second model queued anywhere buys half of
every turn on a model one shares. *How found:* by hand, from the rules;
no test measured GPU time by tenant. *Fix:* the owner's half. A free slot
goes first to the tenant whose turn it is, while it holds fewer than half
the card's slots and has a request to give (`Owner` in `RoundRobin`;
`Picking.owners` in the Lean model; `step_owner`). Riders still get the
next slot after that, so latency on a model that is up stays a matter of
single requests; on a model with one slot the card is the owner's.
(Giving the owner every slot was the other fix considered; it would have
made a rider wait a whole turn, and was rejected for that.)

## 10. When you change the algorithm

Change `policy.go`, `spec/Turns.tla`, `proof/Timeshare/Policy.lean` and §2
here together, rule for rule. Then run `go test ./internal/sched/`,
`nix-build -A tests.tla` and `nix-build -A tests.lean`. If the change
touches a bound, find the new longest wait the way §6.5 does (lower
`MaxWait` until `Bounded` breaks) before you write the formula down.

## 11. The proved code is the running code

The scheduler gpu-timeshare runs is the Lean model. `Decide` and
`RoundRobin` in `policy.go` are the same algorithm in Go: the page to read
beside §2 and the TLA+, and what the tests compare the Lean functions
with. The driver calls neither. (Until 2026-11-10 there were two builds,
and the Go functions decided in the default one. That build is gone.)

How it is put together:

- `proof/Timeshare/Policy.lean` (the model the theorems are about) and
  `proof/Timeshare/Text.lean` (its arguments and answers as text) import
  nothing. `nix-build -A scheduler` has Lean compile them to C and makes
  `libscheduler.a` of the two objects. It needs Lean and not Mathlib, so
  a machine that only runs gpu-timeshare never builds the proofs (no
  binary cache has this Mathlib; building it takes a long time).
  `Text.lean` exports two functions: `timeshare_decide` (a round as text
  in, the actions and the lines as text out) and `timeshare_roundrobin`
  (a model's queued requests in, the picks out).
- `internal/sched/lean.go` links that library and Lean's runtime through
  cgo. `DecideLean` writes `Decide`'s arguments as the text of §8.1 and
  reads the answer; `RoundRobinLean` does the same for `RoundRobin`. The
  log says so at start-up ("the scheduler is the lean one").
- All of Lean's calls are made by one goroutine locked to its thread,
  which the runtime needs.
- `nix-build -A proof` checks the theorems against the same two files.
  Nothing in the build of the binary waits for it: run it (or `-A
  tests.lean`, which needs it) before a change to `Policy.lean` leaves
  the machine it was written on.

What is and is not proved:

- The functions that decide are the ones `mwait_bound`, `settled`,
  `step_owner` and the rest are about. Nothing stands between the
  theorems and the decisions but Lean's compiler and runtime.
- Not proved: `lean.go` (the text going in and coming out) and
  `Text.lean`'s parsing; the driver, which applies the decisions and is
  the model servers' `Env` only by reading; and that the real loads and
  requests keep to *L* and *D*.
- `TestLeanAgrees` checks `DecideLean` against `Decide` on every round of
  60 simulated worlds, with fractional `load_ratio`s, and
  `TestLeanRoundRobinAgrees` checks `RoundRobinLean` against `RoundRobin`
  on 5,000 calls; every other Go test, the end-to-end ones and the VM
  included, runs with the Lean scheduler deciding.

What the text cannot carry is handled on the Go side:

- a `load_ratio` that is not a whole number: each card's load is
  multiplied before it goes in, as `Decide`'s quantum has it;
- in `RoundRobinLean`, names: the model is handed each tenant's place in
  the order of their names, and each key's place of first appearance, so
  any name will do. A tenant served last that has nothing queued now is
  stood for by the tenant before its place, which starts the round at the
  same tenant;
- in `DecideLean`, a name with a space in it: that round is left to Go's
  `Decide`. Config names cannot have one; a client's name could. This is
  the one place the Go algorithm still decides anything.

What it costs: the binary is not static (`CGO_ENABLED=1`; it needs libgmp,
libuv and libstdc++ at run time, which nix gives it: 35 MB of closure with
glibc), it carries Lean's runtime, `go test` needs the library (so: nix,
or `CGO_CFLAGS`/`CGO_LDFLAGS` set as `default.nix` sets them), and each
call is a string built, parsed, and parsed back. And the package is tied
to one Lean: `default.nix`'s own nixpkgs pin, not the caller's.
