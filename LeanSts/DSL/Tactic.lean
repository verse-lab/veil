import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
import LeanSts.TransitionSystem
import LeanSts.DSL.Util
open Lean Lean.Elab.Tactic

/--
  `exact_state` is usually used after `funcases` ar `funcasesM`. At this point the goal should
  contain all state fields as hypotheses. This tactic will then construct the
  state term using the field hypotheses and close the goal.
-/
elab "exact_state" : tactic => do
  let stateTp := (<- stsExt.get).typ
  let .some sn := stateTp.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(mkIdent `State) ..))
  evalTactic $ ← `(tactic| exact $constr)
