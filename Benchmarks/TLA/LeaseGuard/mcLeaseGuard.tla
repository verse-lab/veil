\* Upstream license: MIT; see LICENSE.
\* Copyright (c) 2024 Murat Demirbas
\* Source: https://github.com/muratdem/RaftLeaderLeases/blob/c773c123bdbbf9aeb18031feddd6b291317faf5e/TLA/mcLeaseGuard.tla
\* Modified locally: added this license and source header only.
---- MODULE mcLeaseGuard ----
EXTENDS TLC, leaseGuard

CONSTANTS MaxTerm, MaxLogLen, MaxClock

\* Used for model checking only.
StateConstraint ==
    /\ \A s \in Server :
        /\ currentTerm[s] <= MaxTerm
        /\ Len(log[s]) <= MaxLogLen
        /\ clock <= MaxClock

ServerAndKeySymmetry == Permutations(Server) \union Permutations(Key)

\* This is a "view". The model-checker considers two states equivalent if they
\* produce the same view. We reduce the state space by normalizing entries'
\* timestamps so the smallest time is always 0: e.g., [server1 |-> <<[term |->
\* 1, key |-> k1, index |-> 1, timestamp |-> 2]>>] is the same as [term |-> 1,
\* key |-> k1, index |-> 1, timestamp |-> 99], they are both normalized so the
\* timestamp is 0. Since the spec only cares about time differences, not
\* absolute time, it's safe to normalize times this way and it makes
\* model-checking practical. See Lamport, "Real-Time Model Checking is Really
\* Simple", 2005.

ClockAbstractionView == LET
    allTimes == UNION { { log[s][i].timestamp : i \in 1..Len(log[s]) } : s \in Server }
    start == IF allTimes = {} THEN 0 ELSE Min(allTimes)
    normalizedLog == [
        s \in Server |-> [
            i \in DOMAIN log[s] |-> CreateEntry(log[s][i].term, log[s][i].key, log[s][i].index, log[s][i].timestamp - start)
        ]
    ]
    \* All vars but replace log w/ normalizedLog, omit clock!
    IN [
        currentTerm |-> currentTerm,
        state |-> state,
        normalizedLog |-> normalizedLog,
        matchIndex |-> matchIndex,
        committed |-> committed,
        commitIndex |-> commitIndex,
        latestRead |-> latestRead
    ]

====
