module

public meta import Lean

public meta section

-- NOTE: Adapted from `Mathlib.Tactic.CasesM`, but when cases something, allows giving names
-- to the new hypotheses.

namespace Veil.Util

open Lean Meta Elab Tactic MVarId

partial def casesMatching (matcher : Expr → MetaM (Option α))
    (altNames : α → MetaM (Array Name))
    (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (skipNames : Array Name := #[]) (g : MVarId)
    (keepProjectionNames : Name → Bool := fun _ => false) : MetaM (List MVarId) := do
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
        if skipNames.contains ldecl.userName then continue
        if let some info ← matcher ldecl.type then
          let mut acc := acc
          let keepNames := keepProjectionNames ldecl.userName
          let names ← if allowSplit || keepNames then
            pure ((← altNames info).toList.map ldecl.userName.append)
          else
            pure [ldecl.userName]
          let givenNames := #[{ explicit := true, varNames := names : AltVarNames }]
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId (givenNames := givenNames)
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId (givenNames := givenNames)
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            -- Usually keep the original name for a single field. Some callers
            -- need the complete projection path even for one-field wrappers.
            let g ← match subgoal.fields with
            | #[.fvar fvarId] =>
              if keepNames then pure subgoal.mvarId else subgoal.mvarId.rename fvarId ldecl.userName
            | _ => pure subgoal.mvarId
            if recursive then
              acc ← go g acc
            else
              acc := acc.push g
          return acc
      return (acc.push g)

def casesType (heads : Array Name) (recursive := false) (allowSplit := true) (throwOnNoMatch := true)
    (skipNames : Array Name := #[]) (g : MVarId)
    (keepProjectionNames : Name → Bool := fun _ => false) : MetaM (List MVarId) :=
  let matcher ty := pure <|
    if let .const n .. := ty.headBeta.getAppFn
    then
      if heads.contains n then some n else none
    else none
  let altNames n : MetaM (Array Name) := do
    let .some sinfo := getStructureInfo? (← getEnv) n | return #[]
    pure sinfo.fieldNames
  casesMatching matcher altNames recursive allowSplit throwOnNoMatch skipNames g keepProjectionNames

/-- Common implementation of `cases_type` and `cases_type!`. -/
def elabCasesType (heads : Array Ident)
    (recursive := false) (allowSplit := true) (throwOnNoMatch := true)
    (skipNames : Array Name := #[]) (keepProjectionNames : Name → Bool := fun _ => false) : TacticM Unit := do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic fun g => casesType heads recursive allowSplit throwOnNoMatch skipNames g keepProjectionNames

end Veil.Util
