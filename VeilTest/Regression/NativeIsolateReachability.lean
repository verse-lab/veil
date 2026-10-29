module

public import Veil
public meta import Lean.Util.CollectAxioms

set_option veil.smt.trust false
set_option veil.printCounterexamples false

-- Native actions and unnamed invariants both survive occurrence replay.
veil module NativeCell

individual flag : Bool
after_init { flag := false }
transition keep { flag' = flag }
invariant flag = false

#gen_spec
#check_invariants
end NativeCell

veil module NativeOccurrence

isolate cell : NativeCell
invariant [clear] cell.flag = false

#gen_spec
#check_invariants cell
#check_invariants
#gen_theorems

#check clear.is_inv
#check inst_4_cell__invariant__inv_0.is_inv

-- Initializer and frame helpers must never become environment actions.
example (label : Label) : label = Label.inst_4_cell__procedure__keep := by
  cases label
  rfl

run_cmd do
  let mod ← Veil.getCurrentModule
  unless mod.actions.size == 1 do
    throwError "native replay changed the concrete environment action set"
  unless (← Lean.getEnv).contains
      `NativeOccurrence.inst_4_cell__procedure__keep.frame do
    throwError "native occurrence is missing its semantic frame obligation"
  for name in [`NativeOccurrence.Invariants.is_inv,
      `NativeOccurrence.inst_4_cell__invariant__inv_0.is_inv,
      `NativeOccurrence.clear.is_inv] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "native occurrence reachability depends on an admitted proof"

end NativeOccurrence
