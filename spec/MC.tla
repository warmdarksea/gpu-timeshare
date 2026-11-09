---- MODULE MC ----
\* Timeslice for TLC. The models are interchangeable, so TLC checks one
\* ordering of them for all.
EXTENDS Timeslice, TLC

Sym == Permutations(Models)

\* the claimed bound: a turn lasts at most a load, its timeslice and a
\* drain. A model with work waits out its own drain (if it was on the
\* card), one turn per other model, then its own load.
Turn1 == MaxLoad + MaxTimeslice + MaxDrain
Claim == (Cardinality(Models) - 1) * Turn1 + MaxDrain + MaxLoad
\* one less: TLC must find a wait this long (the claim is tight)
Tight == Claim - 1
====
