module

public meta import Veil.Core.UI.Verifier.TraceCounterexample

/-! Reconstructing a label must specialize dependent parameter types before
adapting SMT values. In particular, SMT represents a Bool value by a Prop. -/

namespace TraceLabelDependentReconstruction

public inductive Label where
  | choose (flag : Bool) (value : if flag then Bool else Nat)

open Lean Elab Command Meta Veil in
run_meta do
  let flagParam : Parameter := { (default : Parameter) with name := `flag, «type» := ← `(Bool) }
  let valueParam : Parameter := { (default : Parameter) with name := `value, «type» := ← `(if flag then Bool else Nat) }
  let proc : ProcedureSpecification := {
    (default : ProcedureSpecification) with info := .action `choose, params := #[flagParam, valueParam] }
  let mod : Veil.Module := {
    (default : Veil.Module) with name := `TraceLabelDependentReconstruction, procedures := #[proc] }
  let values : Std.HashMap (Nat × Nat) Expr :=
    ({} : Std.HashMap (Nat × Nat) Expr) |>.insert (1, 0) (mkConst ``Bool.true) |>.insert (1, 1) (mkConst ``True)
  let some label ← buildLabelFromAction mod #[] `choose 1 values {} | throwError "label reconstruction failed"
  let expected := mkApp2 (mkConst ``Label.choose) (mkConst ``Bool.true) (mkConst ``Bool.true)
  unless ← isDefEq label expected do
    throwError "incorrect dependent label: {label}"

end TraceLabelDependentReconstruction
