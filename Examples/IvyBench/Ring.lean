import Veil
import Veil.Core.Tools.Checker.Concrete.Main

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := *
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

-- safety [single_leader] leader L → le N L
-- invariant pending S D ∧ btw S N D → le N S
-- invariant pending L L → le N L
invariant [unique_lead] leader N ∧ leader M → N = M

#gen_spec

-- #time #check_invariants

instance instBetweenFinEnum (n : Nat): Between (Fin n) where
  btw a b c := (a.val < b.val ∧ b.val < c.val) ∨ (c.val < a.val ∧ a.val < b.val) ∨ (b.val < c.val ∧ c.val < a.val)
  btw_ring a b c := by aesop
  btw_trans w x y z := by omega
  btw_side w x y := by omega
  btw_total w x y := by omega

instance (n' : Nat) (n next : Fin n') : Decidable (∀ (Z : Fin n'), (n = next → False) ∧ (Z ≠ n ∧ Z ≠ next → btw n next Z)) := by
  dsimp [instBetweenFinEnum, Between.btw]
  apply inferInstance

instance (n' : Nat) : (sender n : Fin n') → Decidable (le n sender) := by
  dsimp [TotalOrder.le]
  infer_instance


#gen_exec

#finitizeTypes (Fin 2)


def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => unique_lead ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}


def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
#time #eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end Ring
