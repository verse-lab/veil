import Veil
import Veil.Core.Tools.Checker.Concrete.Main

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

set_option trace.veil.desugar true

veil module Ring

type node
type foo
-- type bar
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

individual x : node
relation leader : node -> Bool
relation pending : node -> node -> Bool
relation xxx : node → foo -> Bool
function ff : node → node
-- NOTE: this causes the issue with deriving the FieldRepresentation and
-- LawfulFieldRepresentation instances commenting it out makes this file compile
-- successfully
function zz : node → foo → node → node
#time #gen_state

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
  let b ← pick Bool
  pending sender n := b  -- FIXME: `pending sender n := *` has bad execution performance
  if (n = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
-- invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L


#gen_spec

-- #time #check_invariants

#gen_exec

#finitize_types (Fin 2), (Fin 2)

#check nextActMultiExec


#check nextVeilMultiExecM
def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => single_leader ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}

def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
-- #time #eval modelCheckerResult'.seen.size

def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end Ring
