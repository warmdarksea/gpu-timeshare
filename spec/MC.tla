---- MODULE MC ----
\* Timeslice for TLC. The models are interchangeable (no sizes: Init picks
\* every packing), so TLC checks one ordering of them for all.
EXTENDS Timeslice, TLC

Sym == Permutations(Models)

\* the claimed bound: a slice lasts at most a load, its timeslice, the
\* load already under way when its time ran out, and a drain; a model
\* with work leads a slice within n of them: what is left of the one it
\* is in, one per other model, then its own load
Slice == MaxLoad + MaxTimeslice + MaxLoad + MaxDrain
Claim == Cardinality(Models) * Slice
====
