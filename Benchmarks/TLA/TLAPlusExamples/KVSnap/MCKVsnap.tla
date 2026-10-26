---- MODULE MCKVsnap ----
\* From tlaplus/Examples.
\* Source: https://github.com/tlaplus/Examples/blob/6a7b26a31c1a6aeec789b455e9bbfa3b3ad2728f/specifications/KeyValueStore/MCKVsnap.tla
\* Copyright (c) 2016: The TLA+ project and other contributors.
\* Upstream MIT license; see ../LICENSE.
EXTENDS KVsnap, TLC
TxIdSymmetric == Permutations(TxId)

\* To get debugging information from KVsnap.tla
BaitInv == TLCGet("level")>7 => ~(\E k1,k2 \in Key: store[k1]#store[k2] /\ k1#k2 /\ store[k1] # NoVal /\ store[k2] # NoVal)

====

