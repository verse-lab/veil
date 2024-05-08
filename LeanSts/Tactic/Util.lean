import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames

open Lean Lean.Elab.Tactic

-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

/-- Is `hyp` an application of `n`, after normalisation? -/
def normalisedIsAppOf (hyp : LocalDecl) (n : Name) : TacticM Bool := do
  let norm ← Meta.reduce (hyp.type) (skipTypes := false)
  return norm.isAppOf n

/-- Returns the hypotheses in `newCtx` that do not appear in `oldCtx`. -/
def newHypotheses (oldCtx : LocalContext) (newCtx : LocalContext) : TacticM (Array LocalDecl) := do
  let mut newHyps := #[]
  for hyp in newCtx do
    if (oldCtx.findFromUserName? hyp.userName |>.isNone) &&
       !hyp.isImplementationDetail then
      newHyps := newHyps.push hyp
  return newHyps

/-- Run the given tactic in all goals. -/
def allGoals [Inhabited α]
  (tac : TacticM α) (comb : List α -> α := fun _ => default)  : TacticM α := do
  if (<- getUnsolvedGoals).length == 0 then
    tac
  else
    withMainContext do
      let mvarIds ← getUnsolvedGoals
      let mut mvarIdsNew := #[]
      let mut ans := []
      for mvarId in mvarIds do
        unless (← mvarId.isAssigned) do
          setGoals [mvarId]
          let (ans', mvarIdsNew') <- withMainContext do
            let mut ans := ans
            let mut mvarIdsNew := mvarIdsNew
            try
              let a <- tac
              ans := a :: ans
              mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
            catch ex =>
              if (← read).recover then
                -- logException ex
                mvarIdsNew := mvarIdsNew.push mvarId
              else
                throw ex
            return (ans, mvarIdsNew)
          (ans, mvarIdsNew) := (ans', mvarIdsNew')
      setGoals mvarIdsNew.toList
      return comb ans
