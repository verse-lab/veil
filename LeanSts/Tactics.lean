import Lean.Elab.Tactic
import LeanSts.TransitionSystem

-- For automation
import Auto
import Duper

-- Tactics to:
-- destruct all `structure`s
-- unfold all definitions (`dsimp`)
-- `repeat' apply And.intro` / `constructor in the goal`
-- call `auto`

-- Plan:
-- (1) Destruct the `next` action
-- RelationalTransitionSystem.next st st'

#check RelationalTransitionSystem.next

open Lean Lean.Elab.Tactic
/-- Destruct a structure into its fields -/
elab "sdestruct " ids:ident* : tactic => withMainContext do
  dbg_trace "sdestruct {ids}"
  let env ← getEnv
  for id in ids do
    let n := getNameOfIdent' id
    let .some info := getStructureInfo? env n
      | throwError "{n} is not a structure"


    return

elab "sts_induction" : tactic => withMainContext do
  let lctx ← Lean.MonadLCtx.getLCtx
  let (_goal, goalType) := (← getMainGoal, ← getMainTarget)
  -- (1) Identify the `next` hypothesis
  let opt_hnext ← lctx.findDeclM? fun (ldecl : Lean.LocalDecl) => do
    let declExpr := ldecl.toExpr
    let declType ← Meta.inferType declExpr
    if declType.isAppOf `RelationalTransitionSystem.next then
      return some ldecl
    else
      return none
  let hnext ← match opt_hnext with
  | none => throwError "sts_induction tactic failed: no `next` hypothesis found"
  | some hnext => pure hnext
  dbg_trace "Found `next` hypothesis: {hnext.toExpr}"
  -- (2) Destruct the `next` hypothesis into individual actions



  return
