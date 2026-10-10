module

public import Veil

set_option linter.unusedVariables false

veil module FirstModule

type node

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  pending n next := true
}

safety [single_leader] leader N ∧ leader M → N = M

#gen_spec

#check_invariants

run_cmd do
  let results ← Veil.Verifier.waitFilteredSync (fun _ => true)
  unless results.totalVCs > 0 && (results.vcs.all fun vc => vc.isDormant || vc.status == some .proven) do
    throwError "This module did not independently complete all of its VCs"

end FirstModule


veil module SecondModule

type node

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  pending n next := true
}

safety [single_leader] leader N ∧ leader M → N = M

#gen_spec

#check_invariants

run_cmd do
  let results ← Veil.Verifier.waitFilteredSync (fun _ => true)
  unless results.totalVCs > 0 && (results.vcs.all fun vc => vc.isDormant || vc.status == some .proven) do
    throwError "This module did not independently complete all of its VCs"

end SecondModule
