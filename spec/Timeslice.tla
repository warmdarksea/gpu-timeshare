---------------------------- MODULE Timeslice ----------------------------
\* gpu-timeshare's scheduler: which model has the card, and when it gives
\* way. internal/sched/policy.go is the same algorithm, rule for rule
\* ([Name] there is the action here); this is its model, for TLC.
\*
\* One model has the card at a time. It keeps it while it has work, and
\* for MaxTimeslice after it loaded if another model waits; then it drains
\* (finishes what it's doing) and leaves. With nothing to do, it leaves at
\* once if another model waits. Waiting models take turns: the one that
\* loaded longest ago goes first.
\*
\* The claim: a model with work spends at most MaxWait not serving (off
\* the card, loading, or draining) before it loads, or runs out of work.
\*
\* Time is discrete (Tick). The scheduler's decisions take no time: Tick
\* can't happen while one is pending. Everything else is an adversary: work
\* arrives and runs out whenever it likes, models take up to MaxLoad to
\* load and MaxDrain to finish what they're doing.
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Models,        \* the models
    MaxTimeslice,  \* ticks a model keeps the card after loading while another waits
    MaxLoad,       \* ticks a model may take to load
    MaxDrain,      \* ticks a model may take to finish its requests in flight
    IdleTicks,     \* ticks an up model must have had no work before it may stop (>= 1)
    MaxWait        \* the claim: no model waits longer than this

ASSUME IdleTicks >= 1

VARIABLES
    st,        \* Models -> {"down", "starting", "up", "draining"}
    work,      \* Models -> BOOLEAN: requests are queued or in flight for it
    order,     \* the turn: the models, the one that loaded longest ago first (LoadedAt, in Go)
    timer,     \* Models -> Nat: ticks spent starting or draining
    age,       \* ticks since the model on the card loaded
    idle,      \* Models -> Nat: ticks up with no work (BusyAt, in Go)
    watched,   \* one model, any of them: the one whose wait is measured
    wait       \* ticks it has had work without serving, since it last loaded or ran dry

vars == <<st, work, order, timer, age, idle, watched, wait>>

Min(a, b) == IF a < b THEN a ELSE b

OnCard     == {m \in Models : st[m] # "down"}
Waiting(m) == work[m] /\ st[m] = "down"
Queued     == \E m \in Models : Waiting(m)
Pos(m)     == CHOOSE i \in 1..Len(order) : order[i] = m
\* the model whose turn it is
Turn       == CHOOSE m \in Models : Waiting(m) /\ \A n \in Models : Waiting(n) => Pos(m) <= Pos(n)
ToBack(m)  == SelectSeq(order, LAMBDA x : x # m) \o <<m>>
Idle(m)    == st[m] = "up" /\ ~work[m]

Leave(m) ==
    /\ st' = [st EXCEPT ![m] = "down"]
    /\ UNCHANGED <<work, order, timer, age, idle, watched, wait>>

-------------------------------------------------------------------------
(* The scheduler. These are the rules of policy.go's Decide.             *)

GiveWay(m)  == Idle(m) /\ Queued /\ Leave(m)
IdleStop(m) == Idle(m) /\ idle[m] >= IdleTicks /\ Leave(m)
Expire(m) ==
    /\ st[m] = "up" /\ work[m] /\ Queued /\ age >= MaxTimeslice
    /\ st' = [st EXCEPT ![m] = "draining"]
    /\ timer' = [timer EXCEPT ![m] = 0]
    /\ UNCHANGED <<work, order, age, idle, watched, wait>>
Start ==
    /\ OnCard = {} /\ Queued
    /\ st' = [st EXCEPT ![Turn] = "starting"]
    /\ timer' = [timer EXCEPT ![Turn] = 0]
    /\ UNCHANGED <<work, order, age, idle, watched, wait>>

Decide == \/ \E m \in Models : GiveWay(m) \/ IdleStop(m) \/ Expire(m)
          \/ Start

-------------------------------------------------------------------------
(* The world.                                                            *)

\* its load starts its time on the card and sends it to the back of the turn
Loaded(m) ==
    /\ st[m] = "starting"
    /\ st' = [st EXCEPT ![m] = "up"]
    /\ age' = 0
    /\ order' = ToBack(m)
    /\ wait' = IF m = watched THEN 0 ELSE wait
    /\ idle' = [idle EXCEPT ![m] = 0]
    /\ UNCHANGED <<work, timer, watched>>

\* a draining model finishes what's in flight (within MaxDrain) and, at
\* once, [Drained] stops it
Drained(m) == st[m] = "draining" /\ Leave(m)

Arrive(m) ==
    /\ ~work[m]
    /\ work' = [work EXCEPT ![m] = TRUE]
    /\ idle' = [idle EXCEPT ![m] = 0]
    /\ UNCHANGED <<st, order, timer, age, watched, wait>>

\* its queue runs dry (or never: a model may have work for ever)
Done(m) ==
    /\ st[m] = "up" /\ work[m]
    /\ work' = [work EXCEPT ![m] = FALSE]
    /\ wait' = IF m = watched THEN 0 ELSE wait
    /\ UNCHANGED <<st, order, timer, age, idle, watched>>

Overdue == \E m \in Models :
    \/ st[m] = "starting" /\ timer[m] >= MaxLoad
    \/ st[m] = "draining" /\ timer[m] >= MaxDrain

Tick ==
    /\ ~ENABLED Decide /\ ~Overdue
    /\ timer' = [m \in Models |-> IF st[m] \in {"starting", "draining"} THEN timer[m] + 1 ELSE timer[m]]
    /\ age' = Min(age + 1, MaxTimeslice)
    /\ wait' = IF work[watched] /\ st[watched] # "up" THEN Min(wait + 1, MaxWait + 1) ELSE wait
    /\ idle' = [m \in Models |-> IF Idle(m) THEN Min(idle[m] + 1, IdleTicks) ELSE 0]
    /\ UNCHANGED <<st, work, order, watched>>

-------------------------------------------------------------------------

Init ==
    /\ st = [m \in Models |-> "down"]
    /\ work = [m \in Models |-> FALSE]
    /\ order \in {s \in [1..Cardinality(Models) -> Models] : \A m \in Models : \E i \in DOMAIN s : s[i] = m}
    /\ timer = [m \in Models |-> 0]
    /\ age = 0
    /\ idle = [m \in Models |-> 0]
    /\ watched \in Models
    /\ wait = 0

Next ==
    \/ Decide
    \/ \E m \in Models : Loaded(m) \/ Drained(m) \/ Arrive(m) \/ Done(m)
    \/ Tick

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* What's claimed.                                                       *)

\* one model on the card at a time
Alone == Cardinality(OnCard) <= 1
\* a model with work spends at most MaxWait ticks not serving before it
\* loads or its work runs out
Bounded == wait <= MaxWait
=============================================================================
