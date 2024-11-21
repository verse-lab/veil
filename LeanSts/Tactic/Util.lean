import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames

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


/-- Iterate over hypotheses to identify the type of the state `Structure`.
    If the state is not found, return `State` as the default. -/
def findStateType (ctx : LocalContext) : TacticM Expr := do
  for hyp in ctx do
    if (hyp.type.isAppOf `RelationalTransitionSystem.init) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.inv) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.safe) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.next)
    then
      return hyp.type.getAppArgs[0]!
  -- TODO: inspect the goal as well, not just the hypotheses
  return (mkConst `State)

/-- Is the given hypothesis a `class` instance (or a `structure`)? -/
def hypIsClass (hyp : LocalDecl) : TacticM Bool := do
  let env ← getEnv
  match hyp.type.getAppFn.constName? with
  | some name => return isStructure env name
  | none => return false

/-- Given a hypothesis, if it's a `Prop`, return its name. If it is
   a `class` or `structure`, return all the names of properties within
   it, e.g. a `TotalOrder` will return `TotalOrder.le_trans`, etc.-/
def collectPropertiesFromHyp (hyp : LocalDecl) : TacticM (Array Name) := do
  let env ← getEnv
  let mut props := #[]
  if ← Meta.isProp hyp.type then
    props := props.push hyp.userName
  if ← hypIsClass hyp then
    let tyctor := hyp.type.getAppFn.constName?.get!
    let .some info := getStructureInfo? env tyctor
      | throwError "{tyctor} has no StructureInfo despite `hypIsClass` returning `true`"
    for field in info.fieldInfo do
      -- FIXME: handle classes that `extend` other classes
      if field.subobject?.isSome then
        continue
      let proj := (env.find? field.projFn).get!
      let isProp ← Meta.isProp proj.type
      if isProp then
        props := props.push field.projFn
  return props

-- FIXME: is there a better way to do this?
def mkSimpName (n : Ident) :=
     mkNode `Lean.Parser.Tactic.simpLemma #[Syntax.node default nullKind #[], Syntax.node default nullKind #[], Syntax.ident SourceInfo.none default n.getId []]
def namesToLemmas (simpIds : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems simpIds
def mkSimpLemmas (simpIds : Array Ident) : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := namesToLemmas (simpIds.map mkSimpName)
