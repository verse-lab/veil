\* Local TLC model for raft.tla (CC BY 4.0; see its header).
\* MCSmall.tla with a bound on the depth of the search, for instances that TLC cannot explore
\* completely. Run it with -workers 1: TLCGet("level") is then the exact depth of a state.
---- MODULE MCDepth ----
EXTENDS MCSmall, TLC

CONSTANT MaxLevel

\* Keeps the states at most MaxLevel - 1 steps from an initial state, whose level is 1.
DepthBound == TLCGet("level") <= MaxLevel
====
