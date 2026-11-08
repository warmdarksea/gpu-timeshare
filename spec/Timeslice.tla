---------------------------- MODULE Timeslice ----------------------------
\* gpu-timeshare's scheduler: which models are on the card, and when they
\* give way. internal/sched/policy.go is the same algorithm, rule for rule
\* ([Name] there is the action here); this is its model, for TLC.
\*
\* The card holds models that fit together. Which sets fit is a *packing*,
\* and Init picks every packing there is, so the model covers any sizes
\* and any capacity. The models on the card form one *slice*. Its *lead*
\* is the model it started with, and its clock starts when the lead has
\* loaded. Waiting models take turns: the one whose last lead is oldest
\* goes first (never: first of all). A waiting model that fits beside the
\* slice joins it, without extending it and without spending its turn.
\* Once the slice has run MaxTimeslice while any model waits, nothing
\* joins any more, and the whole slice drains and leaves.
\*
\* The claim: a model with work spends at most MaxWait off the card before
\* it leads a slice (has the card for MaxTimeslice) or runs out of work.
\* Joining doesn't reset that: a late joiner can drain as it loads.
\*
\* Time is discrete (Tick). The scheduler's decisions take no time: Tick
\* can't happen while one is pending. Everything else is an adversary: work
\* arrives and runs out whenever it likes, models take up to MaxLoad to
\* load and MaxDrain to finish what they're doing.
\*
\* Policy "rotation" is the scheduler before this one, for comparison: each
\* model has its own clock, the first waiting model that fits starts, a
\* model goes to the back of the turn when it leaves, and one that has
\* been up for the period drains alone, if that alone makes room. Its
\* claim is weaker (loading at all counts), and TLC still finds it
\* starving a model.
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Models,        \* the models
    MaxTimeslice,  \* ticks a slice keeps the card while someone waits
    MaxLoad,       \* ticks a model may take to load
    MaxDrain,      \* ticks a model may take to finish its requests in flight
    IdleTicks,     \* ticks an up model must have had no work before it may stop (>= 1)
    MaxWait,       \* the claim: no model waits longer than this
    Policy         \* "timeslice" (this design) or "rotation" (the old one)

ASSUME IdleTicks >= 1

VARIABLES
    fit,       \* the packing: which sets of models fit on the card together (any:
               \* Init picks every one there is, so sizes and capacity are covered)
    st,        \* Models -> {"down", "starting", "up", "draining"}
    work,      \* Models -> BOOLEAN: requests are queued for it
    order,     \* the turn: the models, the one whose last lead is oldest first
    timer,     \* Models -> Nat: ticks spent starting or draining
    age,       \* Models -> Nat: ticks up ("rotation" only)
    idle,      \* Models -> Nat: ticks up with no work (BusyAt, in Go)
    slice,     \* ticks since the slice's lead loaded; -1: not yet, or no slice
    lead,      \* {the slice's lead}, or {} with no slice
    closing,   \* the slice is draining: nothing joins it
    watched,   \* one model, any of them: the one whose wait is measured
    wait       \* ticks off the card with work since it last led a slice or ran dry

vars == <<fit, st, work, order, timer, age, idle, slice, lead, closing, watched, wait>>

Min(a, b) == IF a < b THEN a ELSE b

\* every packing there is: the sets of models that fit together, as a
\* family that holds every single model and every subset of a set in it.
\* Costs and a capacity are one way of making one; this is all of them.
Packings == {F \in SUBSET SUBSET Models :
                /\ \A m \in Models : {m} \in F
                /\ \A S \in F : SUBSET S \subseteq F}

OnCard     == {m \in Models : st[m] # "down"}
Fits(m)    == OnCard \cup {m} \in fit
Waiting(m) == work[m] /\ st[m] = "down"
Pos(m)     == CHOOSE i \in 1..Len(order) : order[i] = m
Before(m, n) == Pos(m) < Pos(n)
ToBack(m)  == SelectSeq(order, LAMBDA x : x # m) \o <<m>>
\* the model whose turn it is
Queued     == \E m \in Models : Waiting(m)
Turn       == CHOOSE m \in Models : Waiting(m) /\ \A n \in Models : Waiting(n) => ~Before(n, m)
Loading    == \E m \in Models : st[m] = "starting"
Idle       == {m \in Models : st[m] = "up" /\ ~work[m]}
\* the slice has had its time, and a model waits: it must go, and nothing
\* joins it any more (joins after its time, while anything waits, can churn
\* for ever: TLC found two ways)
Expired    == Policy = "timeslice" /\ slice >= MaxTimeslice /\ Queued

\* the models in S leave the card; an empty card ends the slice
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] :
                   \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]
LeaveAll(S) ==
    /\ st' = [m \in Models |-> IF m \in S THEN "down" ELSE st[m]]
    /\ order' = IF Policy = "rotation"
                  THEN SelectSeq(order, LAMBDA x : x \notin S) \o SetToSeq(S)
                  ELSE order
    /\ IF OnCard \subseteq S THEN slice' = -1 /\ lead' = {} /\ closing' = FALSE
                             ELSE UNCHANGED <<slice, lead, closing>>
Leave(m) == LeaveAll({m})

-------------------------------------------------------------------------
(* The scheduler. These are the rules of policy.go's Decide.             *)

\* 1. one load at a time; the first waiting model (in turn) that fits. On
\*    an empty card that is the turn's model, and it leads the new slice.
Start(m) ==
    /\ ~closing /\ ~Loading /\ ~Expired
    /\ Waiting(m) /\ Fits(m)
    /\ \A n \in Models : Waiting(n) /\ Fits(n) => ~Before(n, m)
    /\ st' = [st EXCEPT ![m] = "starting"]
    /\ timer' = [timer EXCEPT ![m] = 0]
    /\ lead' = IF OnCard = {} THEN {m} ELSE lead
    /\ UNCHANGED <<work, order, age, idle, slice, closing, watched, wait>>

\* 2. the turn's model doesn't fit, the slice has time left, and stopping
\*    idle models makes room: they stop, together (Decide stops the
\*    largest first until it fits; any set that does is allowed here)
MakeRoom(S) ==
    /\ ~closing /\ ~Loading /\ ~Expired /\ Queued /\ ~Fits(Turn)
    /\ S # {} /\ S \subseteq Idle
    /\ (OnCard \ S) \cup {Turn} \in fit
    /\ LeaveAll(S)
    /\ UNCHANGED <<work, timer, age, idle, watched, wait>>

\* 3. the slice has had its time, and the turn's model doesn't fit: the
\*    whole slice drains
EndSlice ==
    /\ ~closing /\ ~Loading /\ Expired
    /\ closing' = TRUE
    /\ st' = [m \in Models |-> IF st[m] = "up" THEN "draining" ELSE st[m]]
    /\ timer' = [m \in Models |-> IF st[m] = "up" THEN 0 ELSE timer[m]]
    /\ UNCHANGED <<work, order, age, idle, slice, lead, watched, wait>>

\* 3'. the old rule: one busy model up for the period drains, if that
\*     alone makes room
Rotate(m) ==
    /\ Policy = "rotation"
    /\ ~Loading /\ Queued /\ ~Fits(Turn)
    /\ ~\E n \in Models : st[n] = "draining"
    /\ st[m] = "up" /\ work[m] /\ age[m] >= MaxTimeslice
    /\ (OnCard \ {m}) \cup {Turn} \in fit
    /\ st' = [st EXCEPT ![m] = "draining"]
    /\ timer' = [timer EXCEPT ![m] = 0]
    /\ UNCHANGED <<work, order, age, idle, slice, lead, closing, watched, wait>>

Decide == \/ \E m \in Models : Start(m) \/ Rotate(m)
          \/ \E S \in SUBSET Models : MakeRoom(S)
          \/ EndSlice

-------------------------------------------------------------------------
(* The world.                                                            *)

\* the lead's (first) load starts the slice's clock and spends its turn
Loaded(m) ==
    /\ st[m] = "starting"
    /\ st' = [st EXCEPT ![m] = "up"]
    /\ age' = [age EXCEPT ![m] = 0]
    /\ IF m \in lead /\ slice = -1 /\ Policy = "timeslice"
         THEN slice' = 0 /\ order' = ToBack(m)
         ELSE UNCHANGED <<slice, order>>
    /\ wait' = IF m = watched /\ (Policy = "rotation" \/ (m \in lead /\ slice = -1)) THEN 0 ELSE wait
    /\ idle' = [idle EXCEPT ![m] = 0]
    /\ UNCHANGED <<work, timer, lead, closing, watched>>

Drained(m) ==
    /\ st[m] = "draining"
    /\ Leave(m)
    /\ UNCHANGED <<work, timer, age, idle, watched, wait>>

IdleStop(m) ==     \* idle for --idle (Decide's rule; any IdleTicks >= 1 will do)
    /\ m \in Idle /\ idle[m] >= IdleTicks
    /\ Leave(m)
    /\ UNCHANGED <<work, timer, age, idle, watched, wait>>

Arrive(m) ==
    /\ ~work[m]
    /\ work' = [work EXCEPT ![m] = TRUE]
    /\ idle' = [idle EXCEPT ![m] = 0]
    /\ UNCHANGED <<st, order, timer, age, slice, lead, closing, watched, wait>>

\* its queue runs dry (or never: a model may have work for ever)
Done(m) ==
    /\ st[m] = "up" /\ work[m]
    /\ work' = [work EXCEPT ![m] = FALSE]
    /\ wait' = IF m = watched THEN 0 ELSE wait
    /\ UNCHANGED <<st, order, timer, age, idle, slice, lead, closing, watched>>

Overdue == \E m \in Models :
    \/ st[m] = "starting" /\ timer[m] >= MaxLoad
    \/ st[m] = "draining" /\ timer[m] >= MaxDrain

Tick ==
    /\ ~ENABLED Decide /\ ~Overdue
    /\ timer' = [m \in Models |-> IF st[m] \in {"starting", "draining"} THEN timer[m] + 1 ELSE timer[m]]
    /\ age' = [m \in Models |-> IF st[m] = "up" THEN Min(age[m] + 1, MaxTimeslice) ELSE age[m]]
    /\ slice' = IF slice = -1 THEN -1 ELSE Min(slice + 1, MaxTimeslice)
    /\ wait' = IF work[watched] /\ st[watched] # "up" THEN Min(wait + 1, MaxWait + 1) ELSE wait
    /\ idle' = [m \in Models |-> IF st[m] = "up" /\ ~work[m] THEN Min(idle[m] + 1, IdleTicks) ELSE 0]
    /\ UNCHANGED <<st, work, order, lead, closing, watched>>

-------------------------------------------------------------------------

Init ==
    /\ fit \in Packings
    /\ st = [m \in Models |-> "down"]
    /\ work = [m \in Models |-> FALSE]
    /\ order \in {s \in [1..Cardinality(Models) -> Models] : \A m \in Models : \E i \in DOMAIN s : s[i] = m}
    /\ timer = [m \in Models |-> 0]
    /\ age = [m \in Models |-> 0]
    /\ idle = [m \in Models |-> 0]
    /\ slice = -1
    /\ lead = {}
    /\ closing = FALSE
    /\ watched \in Models
    /\ wait = 0

Next ==
    /\ \/ Decide
       \/ \E m \in Models : Loaded(m) \/ Drained(m) \/ IdleStop(m) \/ Arrive(m) \/ Done(m)
       \/ Tick
    /\ UNCHANGED fit

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* What's claimed.                                                       *)

\* the card is never over capacity
UnderCapacity == OnCard \in fit
\* a model with work spends at most MaxWait ticks off the card before it
\* leads a slice (loads at all, for "rotation") or its work runs out
Bounded == wait <= MaxWait
=============================================================================
