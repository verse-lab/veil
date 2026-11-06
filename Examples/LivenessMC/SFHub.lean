module

public import Veil

set_option veil.deferVCGeneration true

/-! # `sfHub` at n = 2: one arbiter and n strongly fair clients, 2n states

An arbiter (location 0) and n clients on their own pair of locations, 2*n states total. The state
space is linear in n while the number of possible combinations of disjuncts in the assumption
grows with 2^n.
Every run passes back through the arbiter, so client 0's request holds infinitely
often and its strong pair is never vacuous.
-/

veil module SFHub

-- `:|` below picks a location from `{a : Nat // a < 2 * n ∧ a ≠ 0}`, which needs this.
public instance (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    Veil.Enumeration {a : Nat // a < n ∧ p a} where
  allValues := ((List.range n).filter p).attachWith _ (by simp)
  complete := by simp

param n : Nat
individual loc : Nat

#gen_state

-- Init == at = 0
after_init { loc := 0 }

-- ToLeaf == at = 0 /\ at' \in Leaves   (Leaves == 1 .. 2*N - 1)
action toLeaf {
  require loc = 0
  let newLoc :| newLoc < 2 * n ∧ newLoc ≠ 0
  loc := newLoc
}

-- ToHub  == at # 0 /\ at' = 0
action toHub {
  require loc ≠ 0
  loc := 0
}

-- Client 0's request is the arbiter itself and its acknowledge is leaf 1; client i > 0 requests at
-- leaf 2i and is acknowledged at leaf 2i+1.
ghost relation reqAt (m : Nat) := loc = 2 * m
ghost relation ackAt (m : Nat) := loc = 2 * m + 1

-- Liveness == [](Req(0) => <>Ack(0)) — a request-response obligation.
-- Does not hold.
temporal [noFair] □ (⌜ reqAt 0 ⌝ → ◇ ⌜ ackAt 0 ⌝)

-- Goal == Fair => Liveness, Fair == \A i \in 0..N-1 : ([]<>Req(i) => []<>Ack(i)).
-- n strong pairs, therefore 2^n combinations of disjuncts in the assumption.
temporal [goalN]
  -- For n = 2 this becomes: (¬ □ ◇ ⌜ reqAt 0 ⌝ ∨ □ ◇ ⌜ ackAt 0 ⌝) ∧ (¬ □ ◇ ⌜ reqAt 1 ⌝ ∨ □ ◇ ⌜ ackAt 1 ⌝)
  -- So four possible combinations of disjuncts in the assumption (e.g. □ ◇ ⌜ ackAt 0 ⌝ ∧ ¬ □ ◇ ⌜ reqAt 1 ⌝)
  (∀ i : Fin n, (□ ◇ ⌜ reqAt i.val ⌝ → □ ◇ ⌜ ackAt i.val ⌝))
  → □ (⌜ reqAt 0 ⌝ → ◇ ⌜ ackAt 0 ⌝)

#gen_spec
#gen_executable

--set_option veil.violationIsError false in
--#temporal_check [noFair] { n := 2 } {}

--set_option veil.violationIsError false in
--#temporal_check [goalN] { n := 2 } {}

end SFHub
