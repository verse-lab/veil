import Lean.Elab.Tactic
import Veil.Util.DSL

open Lean Lean.Elab.Tactic

/-- Is `typ` an application of `n`, after normalisation? -/
def whnfIsAppOf (typ : Expr) (n : Name) : MetaM Bool := do
  let norm ← Meta.whnf typ
  return norm.isAppOf n

def existsBinderName (typ : Expr) : MetaM Name := do
  let norm ← Meta.whnf typ
  match_expr norm with
  | Exists _ body => return body.bindingName!
  | _ => throwError "Expected an existential quantifier, got {norm}"

/-- Returns the hypotheses in `newCtx` that do not appear in `oldCtx`. -/
def newHypotheses (oldCtx : LocalContext) (newCtx : LocalContext) : TacticM (Array LocalDecl) := do
  let mut newHyps := #[]
  for hyp in newCtx do
    if (oldCtx.findFromUserName? hyp.userName |>.isNone) &&
       !hyp.isImplementationDetail then
      newHyps := newHyps.push hyp
  return newHyps

def Veil.run (t: TacticM Syntax): TacticM Unit := Lean.Elab.Tactic.withMainContext do
    evalTactic (<- t)

def Veil.tryGoal (t: TacticM Unit): TacticM Unit := do
  t <|> return ()

def getCtxNames (ctx : LocalContext) : TacticM (Array Name) := do
  let mut hyps := #[]
  for hyp in ctx do
    hyps := hyps.push hyp.userName
  return hyps

/-- Run the given tactic in all goals. -/
def Veil.allGoals [Inhabited α]
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
    If the state is not found, return the DSL state as the default. -/
def findStateType (ctx : LocalContext) : TacticM Expr := do
  for hyp in ctx do
    if (hyp.type.isAppOf `RelationalTransitionSystem.init) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.inv) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.safe) ||
       (hyp.type.isAppOf `RelationalTransitionSystem.next)
    then
      return hyp.type.getAppArgs[0]!
  -- TODO: inspect the goal as well, not just the hypotheses
  let stateName ← getStateName
  return (mkConst stateName)

/-- Is the given hypothesis a `class` instance (or a `structure`)? -/
def hypIsClass (hyp : LocalDecl) : TacticM Bool := do
  let env ← getEnv
  match hyp.type.getAppFn.constName? with
  | some name => return name ≠ ``And ∧ isStructure env name
  | none => return false

/-- Is this type something we should send to the SMT solver? -/
def isHypToCollect (typ : Expr) : MetaM Bool := do
  -- We do not pass inhabitation facts to SMT, as both `lean-auto` and
  -- `lean-smt` choke on them, and solvers already assume all types are
  -- inhabited.
  let isInhabitationFact ← whnfIsAppOf typ ``Nonempty
  return (← Meta.isProp typ) && !isInhabitationFact

/-- Given a hypothesis, if it's a `Prop`, return its name. If it is
   a `class` or `structure`, return all the names of properties within
   it, e.g. a `TotalOrder` will return `TotalOrder.le_trans`, etc.-/
def collectPropertiesFromHyp (hyp : LocalDecl) : TacticM (Array Name) := do
  let env ← getEnv
  let mut props := #[]
  if ← isHypToCollect hyp.type then
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
      if ← isHypToCollect proj.type then
        props := props.push field.projFn
  return props

-- FIXME: is there a better way to do this?
def mkSimpName (n : Ident) :=
     mkNode `Lean.Parser.Tactic.simpLemma #[Syntax.node default nullKind #[], Syntax.node default nullKind #[], Syntax.ident SourceInfo.none default n.getId []]
def namesToLemmas (simpIds : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems simpIds
def mkSimpLemmas (simpIds : Array Ident) : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := namesToLemmas (simpIds.map mkSimpName)
