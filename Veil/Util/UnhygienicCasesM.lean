import Lean

-- NOTE: Adapted from `Mathlib.Tactic.CasesM`, but when cases something, allows giving names
-- to the new hypotheses.

namespace Veil.Util

open Lean Meta Elab Tactic MVarId

partial def casesMatching (matcher : Expr → MetaM (Option α))
    (altNames : α → MetaM (Array Name))
    (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (g : MVarId) : MetaM (List MVarId) := do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
where
  /-- Auxiliary for `casesMatching`. Accumulates generated subgoals in `acc`. -/
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if let some info ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            -- NOTE: Change
            let subNames ← altNames info
            let namePrefix := ldecl.userName
            g.cases ldecl.fvarId (givenNames := #[⟨true, subNames.toList.map namePrefix.append⟩])
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId (givenNames := #[⟨true, [ldecl.userName]⟩])
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            -- If only one new hypothesis is generated, rename it to the original name.
            let g ← match subgoal.fields with
            | #[.fvar fvarId] => subgoal.mvarId.rename fvarId ldecl.userName
            | _ => pure subgoal.mvarId
            if recursive then
              acc ← go g acc
            else
              acc := acc.push g
          return acc
      return (acc.push g)

def casesType (heads : Array Name) (recursive := false) (allowSplit := true) :
    MVarId → MetaM (List MVarId) :=
  let matcher ty := pure <|
    if let .const n .. := ty.headBeta.getAppFn
    then
      if heads.contains n then some n else none
    else none
  let altNames n : MetaM (Array Name) := do
    let .some sinfo := getStructureInfo? (← getEnv) n | return #[]
    pure sinfo.fieldNames
  casesMatching matcher altNames recursive allowSplit

/-- Common implementation of `cases_type` and `cases_type!`. -/
def elabCasesType (heads : Array Ident)
    (recursive := false) (allowSplit := true) : TacticM Unit := do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic (casesType heads recursive allowSplit)

end Veil.Util
