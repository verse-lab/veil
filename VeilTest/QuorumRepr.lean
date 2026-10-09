module

public import Veil

/-!
`Veil.BitVecAsFinset α` (`Veil/Frontend/DSL/State/BitVecAsFinset.lean`) is a subset of a finitely encodable type stored as a
bit vector; `Quorum α`, `MinQuorum α` and `ByzNSet α` are built on it. Everywhere such a
set is displayed, it must read as the set of its members, not as a bit vector: in `#eval`,
in enumerations, in JSON, and in the action labels of a model-checker trace.
-/

open Veil

def q01 : Quorum (Fin 3) := ⟨BitVecAsFinset.ofList [0, 1], by decide⟩

/-- info: {0, 1} -/
#guard_msgs in
#eval q01

/-- info: [{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}] -/
#guard_msgs in
#eval (Enumeration.allValues (α := Quorum (Fin 3)))

-- `MinQuorum` keeps only the majorities of minimal size, as a TLC configuration would list.
/-- info: [{0, 1}, {0, 2}, {1, 2}] -/
#guard_msgs in
#eval (Enumeration.allValues (α := MinQuorum (Fin 3)))

/-- info: [{}, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}] -/
#guard_msgs in
#eval (Enumeration.allValues (α := ByzNSet (Fin 3)))

-- The JSON form (used by model-checker traces) is the same string.
/-- info: "{0, 1}" -/
#guard_msgs in
#eval IO.println (Lean.toJson q01).compress

public class QuorumOf (acceptor : outParam Type) (quorum : Type) where
  member : acceptor → quorum → Bool

public instance : QuorumOf (Fin 3) (Quorum (Fin 3)) where
  member a q := decide (a ∈ q)

veil module QuorumRepr

type acceptor
type quorum

instantiate qm : QuorumOf acceptor quorum
open QuorumOf

relation voted (a : acceptor)
individual decided : Bool

#gen_state

after_init {
  voted A := false
  decided := false
}

action vote (a : acceptor) {
  voted a := true
}

action decide (q : quorum) {
  require ∀ a, member a q → voted a
  decided := true
}

-- Violated on purpose: the trace shows the quorum chosen by `decide`.
invariant [never_decided] ¬ decided

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: never_decided)
  State 0 (via init):
    decided = false
    voted = []
  State 1 (via vote(a=0)):
    decided = false
    voted = [0]
  State 2 (via vote(a=1)):
    decided = false
    voted = [0, 1]
  State 3 (via decide(q={0, 1})):
    decided = true
    voted = [0, 1]
-/
#guard_msgs in
#model_check interpreted { acceptor := Fin 3, quorum := Quorum (Fin 3) } {} (sequential := true)

end QuorumRepr
