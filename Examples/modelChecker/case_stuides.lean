/-
# Model Checker Case Studies Statistics

| Index | Case Study               | Source              | work process              |
────────|──────────────────────────|─────────────────────|───────────────────────────
| 1     | Diehard                  | TLC bench           | ✅
| 2     | room                     | TLC bench           | ✅
| 3     | puzzle                   | TLC repo            | ✅
| 4     | AWSDNSRace               | TLC                 | ✅
| 5     | aws                      | TLC                 | ✅AWS service verification |
────────|──────────────────────────|─────────────────────|───────────────────────────
| 6     | `Bakery`                 | TLC /Apalache       | `ghost relation` can not work properly yet |
| 7     | Peterson                 | TLC repo            | ✅
| 8     | TwoPhaseCommit           | TLC /Apalache       | ✅
| 9     | SimpleAllocator          | TLC /Apalache       | ✅
| 10    | keyValueStore            | TLC repo            | ✅
| 11    | Prisoners                | TLC /Apalache       | ✅
| 12    | EWD840                   | TLC bench/Apalache  | ✅
────────|──────────────────────────|─────────────────────|───────────────────────────
| 13    | MultiSigAll              | IvyBench            | ✅
| 14    | Ring                     | IvyBench            | wip
| 15    | RicardAgrawala           | IvyBench            | ✅
| 16    | `PaxosEPR?`              | IvyBench            | `assumption` can not work properly yet |
| 17    | `MultiSigMajority?`      | IvyBench            | `assumption` can not work properly yet |
|-------|──────────────────────────|---------------------|--------------------------|
| 18    | 0_mutex_deadlock         | ATC'25 (TLC)        | ✅ Deadlock detection verification |
| 19    | 1_mutex_mutual_exclusion | ATC'25 (TLC)        | ✅ Mutex mutual exclusion verification |
| 20    | spinLock                 | ATC'25 (TLC)        | ✅ Spin lock implementation |
| 21    | structure                | ATC'25 (TLC)        | ✅ We can use built-in `structure` in lean.
────────|──────────────────────────|─────────────────────|───────────────────────────
| 22    | `NOPaxos?`               |                     | some issues with `non-determisim`  |
| 23    | `Raft??`                 |                     |
| 24    | `bcastByz?`              |                     |


* We use group 1 and group 2 to demonstate (easy to understand) how can we spcecify and verify classic TLC examples.

* We use group 3 to show how our model checker can work as a complementary tool for the verifier.

* We need group 4 and group 5 to demonstrate how our model checker can work as a standalone tool to verify real-world protocols,
finding bugs and running them.
-/
