import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/distai/ivy/Ricart-Agrawala.ivy


veil module RicartAgrawala


type node

enum thread = {T1, T2, T3}

relation requested (n1 : node) (n2 : node)
relation replied (n1 : node) (n2 : node)
relation holds (n : node)

#gen_state

after_init {
  requested N1 N2 := false;
  replied N1 N2 := false;
  holds N := false
}

action request (requester: node) (responder : node) {
  require ¬ requested requester responder;
  require requester ≠ responder;
  requested requester responder := true
}

action reply (requester: node) (responder: node) {
    -- require ¬ replied requester responder;
    require ¬ holds responder;
    -- require ¬ replied responder requester;
    require requested requester responder;
    require requester ≠ responder;
    requested requester responder := false;
    replied requester responder := true
}

action enter (requester: node) {
  require ∀ N, (N ≠ requester) → replied requester N;
  holds requester := true
}

action leave (requester : node) {
  require holds requester;
  holds requester := false;
  replied requester N := false
}

safety [mutual_exclusion] (holds N1 ∧ holds N2) → N1 = N2
invariant [aux_1] N1 ≠ N2 → ¬(replied N1 N2 ∧ replied N2 N1)
invariant [aux_2] (N1 ≠ N2 ∧  holds N1) → replied N1 N2

#gen_spec

#time #check_invariants


#gen_exec
#finitizeTypes thread, thread
def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => mutual_exclusion ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}

def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
#eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end RicartAgrawala
