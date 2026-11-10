------------------------------ MODULE Turns ------------------------------
\* gpu-timeshare's scheduler: which model is on which card, whose turn it
\* is, and when a turn ends. internal/sched/policy.go is the same
\* algorithm, rule for rule ([Name] there is the action here); this is its
\* model, for TLC. doc/VERIFICATION.md describes both.
\*
\* A flow is one tenant's requests for one model. A card holds one model
\* at a time, and its time is cut into turns; a turn belongs to a tenant.
\* Tenants with queued requests stand in one line, and each tenant keeps a
\* line of its own models; newcomers join at the back. A tenant goes to the
\* back when a turn of its ends, and a model (in every tenant's line) when
\* it leaves a card. A model keeps its card while it has work, and until
\* its turn is MaxTimeslice old if somebody else has a better claim.
\*
\* The claim (Bounded): a flow with queued requests spends at most MaxWait
\* with its model not up, whatever the other tenants do.
\*
\* Time is discrete (Tick). The scheduler's decisions take no time: Tick
\* can't happen while one is pending. Everything else is an adversary:
\* requests arrive and are taken whenever they like, loads take up to
\* MaxLoad or fail, requests in flight take up to MaxDrain, a model is
\* short of cards whenever it says so.
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Tenants, Models, Cards,
    MaxTimeslice,  \* ticks a turn lasts before it can be taken
    MaxLoad,       \* ticks a model may take to load
    MaxDrain,      \* ticks a card may take to finish its requests in flight
    MaxWait,       \* the claim: no flow waits longer than this
    MaxBurst       \* the claim: a round is at most this many decisions

\* A turn that began this instant can't be taken (policy.go's winner): here
\* that is MaxTimeslice >= 1, since a new turn's clock is 0. With 0, two
\* tenants on one model would pass the turn between them without end.
ASSUME MaxTimeslice >= 1

None == "none"

VARIABLES
    st,       \* Cards -> {"down", "starting", "up", "draining"}
    on,       \* Cards -> the model on it (None when down)
    owner,    \* Cards -> the tenant whose turn it is (None when down)
    clock,    \* Cards -> ticks: starting, of this turn, or draining
    busy,     \* Cards -> BOOLEAN: requests are in flight on it
    q,        \* Tenants -> Models -> BOOLEAN: the flow has queued requests
    more,     \* Models -> BOOLEAN: it has more queued than its cards can take
    line,     \* the tenants with queued requests, the first to be served first
    mline,    \* Tenants -> its models with queued requests, likewise
    watched,  \* one flow <<tenant, model>>, any of them: its wait is measured
    wait,     \* ticks it has had queued requests while its model was not up
    burst     \* decisions since anything else happened

vars == <<st, on, owner, clock, busy, q, more, line, mline, watched, wait, burst>>

Min(a, b)    == IF a < b THEN a ELSE b
Range(s)     == {s[i] : i \in DOMAIN s}
Without(s, x) == SelectSeq(s, LAMBDA y : y # x)
ToBack(s, x) == IF x \in Range(s) THEN Without(s, x) \o <<x>> ELSE s
Pos(s, x)    == CHOOSE i \in DOMAIN s : s[i] = x
\* the first of s that is in S (S must hold one)
First(s, S)  == s[CHOOSE i \in DOMAIN s : s[i] \in S /\ \A j \in 1..(i-1) : s[j] \notin S]

Serving(c)  == st[c] \in {"starting", "up"}
Placed(m)   == \E c \in Cards : Serving(c) /\ on[c] = m
HasWork(m)  == \E t \in Tenants : q[t][m]
Unplaced(m) == HasWork(m) /\ ~Placed(m)
Short(m)    == HasWork(m) /\ Placed(m) /\ more[m]
Held(t)     == Cardinality({c \in Cards : Serving(c) /\ owner[c] = t})
Idle(c)     == st[c] = "up" /\ ~busy[c] /\ ~HasWork(on[c])

\* what a tenant would put on a free card: a model of its own that is on
\* no card, else one that is short of cards
Wants(t)    == {m \in Models : q[t][m] /\ (Unplaced(m) \/ Short(m))}
Claims      == {t \in Tenants : Wants(t) # {}}
Lost(t)     == {m \in Models : q[t][m] /\ Unplaced(m)}
AnyLost     == \E t \in Tenants : Lost(t) # {}
StartPick(t) == IF Lost(t) # {} THEN First(mline[t], Lost(t)) ELSE First(mline[t], Wants(t))
\* fewest cards first, then the line
Ahead(t, u) == Held(t) < Held(u) \/ (Held(t) = Held(u) /\ Pos(line, t) < Pos(line, u))
NextClaim   == CHOOSE t \in Claims : \A u \in Claims \ {t} : Ahead(t, u)

\* a turn on c ends: its tenant goes to the back of the line, and its model
\* to the back of every tenant's (they all had it)
Ended(c) ==
    /\ line' = ToBack(line, owner[c])
    /\ mline' = [t \in Tenants |-> ToBack(mline[t], on[c])]

Decision == burst' = burst + 1

-------------------------------------------------------------------------
(* The scheduler. These are the rules of policy.go's Decide.             *)

\* a draining card with nothing in flight stops
Drained(c) ==
    /\ st[c] = "draining" /\ ~busy[c]
    /\ st' = [st EXCEPT ![c] = "down"]
    /\ on' = [on EXCEPT ![c] = None]
    /\ owner' = [owner EXCEPT ![c] = None]
    /\ Decision
    /\ UNCHANGED <<clock, busy, q, more, line, mline, watched, wait>>

\* a turn begins: the first claim gets the free card
Start(c) ==
    /\ st[c] = "down" /\ Claims # {}
    /\ LET t == NextClaim
           m == StartPick(t)
       IN /\ st' = [st EXCEPT ![c] = "starting"]
          /\ on' = [on EXCEPT ![c] = m]
          /\ owner' = [owner EXCEPT ![c] = t]
          /\ clock' = [clock EXCEPT ![c] = 0]
    /\ Decision
    /\ UNCHANGED <<busy, q, more, line, mline, watched, wait>>

\* a turn ends without a drain: the card stops, its tenant goes to the back
Stop(c) ==
    /\ st' = [st EXCEPT ![c] = "down"]
    /\ on' = [on EXCEPT ![c] = None]
    /\ owner' = [owner EXCEPT ![c] = None]
    /\ Ended(c)
    /\ UNCHANGED <<clock, busy, q, more, watched, wait>>

\* an idle card stops at once when a model is on no card and no card is free
\* (not for a copy: an idle model is warm, and a copy is only a speed-up)
GiveWay(c) ==
    /\ Idle(c) /\ AnyLost /\ \A d \in Cards : st[d] # "down"
    /\ Stop(c) /\ Decision

\* [Expire]. The turn on c is MaxTimeslice old. Who has the best claim to
\* the card now? A tenant can stay (it has queued requests for the model
\* that is there), move (a model of its own is on no card), or copy (a
\* model of its own is short of cards, and it would still hold fewer cards
\* than the owner afterwards). Fewest cards first, then the line; the
\* owner, who has had its turn, counts one card fewer and comes last among
\* equals.
CanStay(c, t) == q[t][on[c]]
CanMove(c, t) == Lost(t) # {}
Copies(c, t)  == {m \in Models : q[t][m] /\ Short(m) /\ m # on[c]}
CanCopy(c, t) == t # owner[c] /\ Held(t) + 2 <= Held(owner[c]) /\ Copies(c, t) # {}
Cand(c)       == {t \in Range(line) : CanStay(c, t) \/ CanMove(c, t) \/ CanCopy(c, t)}
Rank(c, t)    == <<Held(t) - (IF t = owner[c] THEN 1 ELSE 0), IF t = owner[c] THEN 1 ELSE 0, Pos(line, t)>>
Less(a, b)    == \/ a[1] < b[1]
                 \/ a[1] = b[1] /\ a[2] < b[2]
                 \/ a[1] = b[1] /\ a[2] = b[2] /\ a[3] < b[3]
Winner(c)     == CHOOSE t \in Cand(c) : \A u \in Cand(c) \ {t} : Less(Rank(c, t), Rank(c, u))
\* what the tenant would have on c: its first model that is on no card;
\* if it has none, the one that is there; else a copy
Pick(c, t)    == IF Lost(t) # {} THEN First(mline[t], Lost(t))
                 ELSE IF q[t][on[c]] THEN on[c]
                 ELSE First(mline[t], Copies(c, t))
Expired(c)    == /\ st[c] = "up" /\ clock[c] >= MaxTimeslice /\ Cand(c) # {}
                 /\ \A d \in Cards : st[d] # "draining"

Passes(c)     == Expired(c) /\ Winner(c) # owner[c] /\ Pick(c, Winner(c)) = on[c]

\* the winner wants the model that is there: the turn passes, nothing swaps
Pass(c) ==
    /\ Expired(c)
    /\ LET t == Winner(c) IN
        /\ Passes(c)
        /\ owner' = [owner EXCEPT ![c] = t]
        /\ clock' = [clock EXCEPT ![c] = 0]
        /\ line' = ToBack(line, owner[c])
    /\ Decision
    /\ UNCHANGED <<st, on, busy, q, more, mline, watched, wait>>

\* the winner wants another model (and no free card can have it, and no turn
\* can pass instead): the card takes no more requests and
\* finishes the ones in flight
Drain(c) ==
    /\ Expired(c)
    /\ Pick(c, Winner(c)) # on[c]
    /\ \A d \in Cards : st[d] # "down" /\ ~Passes(d)
    /\ st' = [st EXCEPT ![c] = "draining"]
    /\ clock' = [clock EXCEPT ![c] = 0]
    /\ Ended(c)
    /\ Decision
    /\ UNCHANGED <<on, owner, busy, q, more, watched, wait>>

Decide == \E c \in Cards : Drained(c) \/ Start(c) \/ GiveWay(c) \/ Pass(c) \/ Drain(c)

-------------------------------------------------------------------------
(* The world.                                                            *)

World == burst' = 0

WatchedUp == \E c \in Cards : st[c] = "up" /\ on[c] = watched[2]

Loaded(c) ==
    /\ st[c] = "starting"
    /\ st' = [st EXCEPT ![c] = "up"]
    /\ clock' = [clock EXCEPT ![c] = 0]
    /\ wait' = IF on[c] = watched[2] THEN 0 ELSE wait
    /\ World
    /\ UNCHANGED <<on, owner, busy, q, more, line, mline, watched>>

\* a load fails, or a server dies at work: the turn is over all the same.
\* (Not the watched model: the claim is about a model that loads when it
\* is asked to. The driver refuses a failing model's requests.)
Fail(c) ==
    /\ Serving(c) /\ on[c] # watched[2]
    /\ busy' = [busy EXCEPT ![c] = FALSE]
    /\ Stop(c) /\ World

\* an idle card stops after the idle time, whenever that is
IdleStop(c) == Idle(c) /\ Stop(c) /\ World

Arrive(t, m) ==
    /\ ~q[t][m]
    /\ q' = [q EXCEPT ![t][m] = TRUE]
    /\ line' = IF t \in Range(line) THEN line ELSE Append(line, t)
    /\ mline' = [mline EXCEPT ![t] = Append(@, m)]
    /\ World
    /\ UNCHANGED <<st, on, owner, clock, busy, more, watched, wait>>

\* the flow's last queued request goes to a card that has its model up
Taken(t, m, c) ==
    /\ q[t][m] /\ st[c] = "up" /\ on[c] = m
    /\ q' = [q EXCEPT ![t][m] = FALSE]
    /\ busy' = [busy EXCEPT ![c] = TRUE]
    /\ mline' = [mline EXCEPT ![t] = Without(@, m)]
    /\ line' = IF \E n \in Models \ {m} : q[t][n] THEN line ELSE Without(line, t)
    /\ wait' = IF <<t, m>> = watched THEN 0 ELSE wait
    /\ World
    /\ UNCHANGED <<st, on, owner, clock, more, watched>>

\* requests go in flight (the flow still has more queued), and finish
Work(c) ==
    /\ st[c] = "up" /\ HasWork(on[c]) /\ ~busy[c]
    /\ busy' = [busy EXCEPT ![c] = TRUE]
    /\ World
    /\ UNCHANGED <<st, on, owner, clock, q, more, line, mline, watched, wait>>

Finish(c) ==
    /\ busy[c]
    /\ busy' = [busy EXCEPT ![c] = FALSE]
    /\ World
    /\ UNCHANGED <<st, on, owner, clock, q, more, line, mline, watched, wait>>

Flip(m) ==
    /\ more' = [more EXCEPT ![m] = ~@]
    /\ World
    /\ UNCHANGED <<st, on, owner, clock, busy, q, line, mline, watched, wait>>

Overdue == \E c \in Cards :
    \/ st[c] = "starting" /\ clock[c] >= MaxLoad
    \/ st[c] = "draining" /\ busy[c] /\ clock[c] >= MaxDrain

Tick ==
    /\ ~ENABLED Decide /\ ~Overdue
    /\ clock' = [c \in Cards |-> IF st[c] = "down" THEN clock[c]
                                 ELSE IF st[c] = "up" THEN Min(clock[c] + 1, MaxTimeslice)
                                 ELSE clock[c] + 1]
    /\ wait' = IF q[watched[1]][watched[2]] /\ ~WatchedUp THEN Min(wait + 1, MaxWait + 1) ELSE wait
    /\ World
    /\ UNCHANGED <<st, on, owner, busy, q, more, line, mline, watched>>

-------------------------------------------------------------------------

Init ==
    /\ st = [c \in Cards |-> "down"]
    /\ on = [c \in Cards |-> None]
    /\ owner = [c \in Cards |-> None]
    /\ clock = [c \in Cards |-> 0]
    /\ busy = [c \in Cards |-> FALSE]
    /\ q = [t \in Tenants |-> [m \in Models |-> FALSE]]
    /\ more = [m \in Models |-> FALSE]
    /\ line = <<>>
    /\ mline = [t \in Tenants |-> <<>>]
    /\ watched \in Tenants \X Models
    /\ wait = 0
    /\ burst = 0

Next ==
    \/ Decide
    \/ \E c \in Cards : Loaded(c) \/ Fail(c) \/ IdleStop(c) \/ Work(c) \/ Finish(c)
    \/ \E t \in Tenants, m \in Models : Arrive(t, m) \/ \E c \in Cards : Taken(t, m, c)
    \/ \E m \in Models : Flip(m)
    \/ Tick

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* What's claimed.                                                       *)

\* the lines are exactly the tenants, and the models, with queued requests
Lines ==
    /\ Range(line) = {t \in Tenants : \E m \in Models : q[t][m]}
    /\ Len(line) = Cardinality(Range(line))
    /\ \A t \in Tenants : /\ Range(mline[t]) = {m \in Models : q[t][m]}
                          /\ Len(mline[t]) = Cardinality(Range(mline[t]))
\* a card that is down has nothing in flight: the scheduler never stops a
\* card that is answering (only a failure does)
NoKill == \A c \in Cards : st[c] = "down" => ~busy[c]
\* once a round has settled, no card is free while a model wants one, and
\* none is idle while a model is on no card
NoWaste == ~ENABLED Decide =>
    /\ (Claims = {} \/ \A c \in Cards : st[c] # "down")
    /\ (~AnyLost \/ \A c \in Cards : ~Idle(c))
\* a round settles
Settles == burst <= MaxBurst
\* a flow with queued requests spends at most MaxWait with its model not up
Bounded == wait <= MaxWait
=============================================================================
