---- MODULE MC ----
\* Turns for TLC. Tenants, models and cards are interchangeable, so TLC
\* checks one ordering of each for all.
EXTENDS Turns, TLC

\* how many models the watched flow's tenant has queued requests for at a
\* time, at most (the number of models: no limit)
CONSTANT K

Sym == Permutations(Tenants) \cup Permutations(Models) \cup Permutations(Cards)

Narrow == Cardinality({m \in Models : q'[watched[1]][m]}) <= K

T == Cardinality(Tenants)
M == Cardinality(Models)
\* a turn lasts at most a load, its timeslice and a drain
Turn1 == MaxLoad + MaxTimeslice + MaxDrain
\* The claimed bound, in turns that others (or other models) have while the
\* flow waits. Its tenant has a turn for each of its models that were ahead
\* in its line (at most K - 1), and before each of those and the one that
\* loads the flow's model, every other tenant has one: T * K - 1. One more
\* may be running when the wait begins: T * K. And never more than
\* T * (M - 1): a turn of another tenant's on a model that was ahead takes
\* it from ahead. Then the flow's own load -- after its own drain, if its
\* model was up when the wait began.
Turns == IF T * K < T * (M - 1) THEN T * K ELSE T * (M - 1)
Claim == Turns * Turn1 + MaxDrain + MaxLoad
\* one less: where the claim is exact, TLC must find a wait this long
Tight == Claim - 1
\* a round: each card at most drains, stops and starts
Burst == 3 * Cardinality(Cards)
====
