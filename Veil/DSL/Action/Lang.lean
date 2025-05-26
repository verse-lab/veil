import Lean
import Lean.Parser
import Veil.Model.State
import Veil.Util.DSL
import Veil.DSL.Base
import Veil.DSL.Internals.StateExtensions
import Veil.DSL.Action.Syntax
import Veil.DSL.Action.Theory

open Lean Elab Command Term Meta Lean.Parser

/-! # Action Language

This file defines the syntax for the imperative language we use to
define initializers and actions.
-/

section Veil

attribute [actSimp] modify modifyGet MonadStateOf.modifyGet get
  getThe MonadStateOf.get MonadStateOf.set instMonadStateOfMonadStateOf
  instMonadStateOfWp

macro "unfold_wp" : conv =>
  `(conv| unfold
    -- unfold actions defined via Veil do-notation
    Wp.pure
    Wp.bind
    Wp.assume
    Wp.assert
    Wp.require
    Wp.fresh
    Wp.get
    -- unfold state monad actions
    set
    modify
    modifyGet
    get
    instMonadStateOfMonadStateOf
    getThe
    MonadStateOf.modifyGet
    MonadStateOf.get
    MonadStateOf.set
    instMonadStateOfWp
    -- unfold specifications
    Wp.spec
    -- unfold actions defined by conversion
    Wp.toWlp
    Wp.toBigStep
    Wp.toTwoState
    BigStep.toWp
    Function.toWp
    -- unfold actions definded via lifting
    monadLift
    getFrom
    setIn
    instMonadLiftTOfMonadLift
    MonadLift.monadLift
    instMonadLiftWpOfIsSubStateOf
    instMonadLiftT)

partial def getCapitals (s : Syntax) :=
  let rec loop  (acc : Array $ TSyntax `ident ) (s : Syntax) : Array $ TSyntax `ident :=
    if s.isIdent then
      if isCapital s then
        acc.push ⟨s⟩
      else
        acc
    else
      s.getArgs.foldl (init := acc) loop
  (loop #[] s).toList.eraseDups.toArray

/-- Close the given expression under all capital letters.
    this is called for `require`, `safety` and `invariant` -/
def closeCapitals (s : Term) : MacroM Term :=
  let caps := getCapitals s
  `(forall $[$caps]*, $s)

/-- Throw an error if the field (which we're trying to assign to) was
declared immutable. -/
def throwIfImmutable' (nm : Name) (isTransition : Bool := false) : TermElabM Unit := do
  -- NOTE: This code supports two modes of operation:
  -- (a) child modules' state is immutable in the parent
  -- (b) child modules' state mutability annotations are inherited in the parent
  let spec := (← localSpecCtx.get).spec
  let .some comp := spec.getStateComponent nm.components[0]!
    | throwError "trying to assign to undeclared state component {nm}"
  if comp.isModule && comp.isImmutable then -- (a)
    throwError "cannot assign to {nm}: child module's ({comp.name}) state is immutable in the parent ({spec.name})"
  else -- (b)
    let (modules, field, spec) ← getInnerMostModule nm
    trace[veil.debug] "{nm} ({comp}) → assigning to field {ppModules modules}.{field} (declared in module {spec.name})"
    let .some comp := spec.getStateComponent field
      | throwError "trying to assign to undeclared state component {nm} (fully qualified name: {ppModules modules}.{field})"
    if comp.isImmutable then
      let msg := if isTransition then "the transition might modify" else "trying to assign to"
      let explanation := if isTransition then s!" (since it mentions its primed version {mkPrimed comp.name})" else ""
      throwError "{comp.kind} {comp.name} in module {spec.name} was declared immutable, but {msg} it{explanation}!"
  where
  ppModules (modules : Array Name) := ".".intercalate $ Array.toList $ modules.map (·.toString)
  getInnerMostModule (nm : Name) : TermElabM (Array Name × Name × ModuleSpecification) := do
    let mut spec := (← localSpecCtx.get).spec
    let field := nm.updatePrefix default
    let mut path := let mods := nm.components.toArray; mods[:mods.size - 1]
    -- This contains the full names of the modules in the path to the field
    let mut modules : Array Name := #[]
    while true do
      let .some (topComp, path') := path.popHead?
        | break
      let .some topComp := spec.getStateComponent topComp
        | throwError "trying to assign to {nm}, but {topComp} is not a declared field in {ppModules modules}"
      let .some topModule := topComp.moduleName
        | throwError "(internal error) {topComp} has no module name in its StateComponent definition"
      modules := modules.push topModule
      path := path'
      match (← globalSpecCtx.get)[topModule]? with
      | .some mod => spec := mod.spec
      | .none => throwError "trying to assign to {nm}, but {topModule} (the module type of {topComp} in {path}) is not a declared module"
    return (modules, field, spec)

def throwIfImmutable (lhs : TSyntax `Lean.Parser.Term.structInstLVal) : TermElabM Unit := do
  let nm ← getIdFrom lhs
  throwIfImmutable' nm
  where getIdFrom (lhs : TSyntax `Lean.Parser.Term.structInstLVal) : TermElabM Name :=
    match lhs with
    | `(Lean.Parser.Term.structInstLVal|$id:ident) => pure id.getId
    | _ => throwErrorAt lhs "expected an identifier in the LHS of an assignment, got {repr lhs}"

def getFields [Monad m] [MonadEnv m] : m (Array Name) := do
  let spec := (← localSpecCtx.get).spec
  pure $ spec.signature.map (·.name)

partial def getFieldsRecursively [Monad m] [MonadEnv m] [MonadError m]: m (Array Name) := do
  let spec := (← localSpecCtx.get).spec
  let res ← go spec #[]
  return res
  where
  go (spec : ModuleSpecification) (path : Array Name) : m (Array Name) := do
    let mut fields := #[]
    for comp in spec.signature do
      match comp.kind with
      | .module =>
        let .some modName := comp.moduleName
          | throwError s!"(internal error) {comp} has no module name in its StateComponent definition"
        let spec' := (← globalSpecCtx.get)[modName]!.spec
        fields := fields ++ (← go spec' (path.push comp.name))
      | _ => fields := fields.push (mkNameFromComponents (path.push comp.name).toList)
    return fields

def getUnchangedFields [Monad m] [MonadEnv m] [MonadError m] (used : Name → Bool): m (Array Ident) := do
  let fields ← getFieldsRecursively
  let unchangedFields := fields.filterMap (fun f => if !used f then some $ mkIdent f else none)
  return unchangedFields

def getChangedFields [Monad m] [MonadEnv m] [MonadError m] (used : Name → Bool): m (Array Ident) := do
  let fields ← getFieldsRecursively
  let unchangedFields := Std.HashSet.ofArray $ (← getUnchangedFields used).map (fun (x : Ident) => x.getId)
  let changedFields := fields.filter (fun f => !unchangedFields.contains f)
  pure $ changedFields.map mkIdent

def getSubInitializers [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m]: m (Array (Ident × Term)) := do
  let mut names := #[]
  let ourSpec := (← localSpecCtx.get).spec
  for (modAlias, _) in ourSpec.dependencies do
    let initName := mkIdent <| modAlias ++ `initializer
    let initTerm <- `(@$initName $(← ourSpec.arguments)*)
    names := names.push (initName, initTerm)
  return names

def getSubProcedures : TermElabM (Array (Ident × Term)) := do
  /- FIXME: this replicates some of the logic in `defineDepsActions`, since when
  this gets called as part of `defineDepsActions` (invoked indirectly in the
  elaboration of the `action` to be defined -- see `do'` elaborator), the list
  of actions (which _should_ contain actions from dependent modules) is empty,
  since we haven't yet `monadLift`ed them to the parent (dependee) model's state
  definition. -/
  let mut names := #[]
  let ourSpec := (← localSpecCtx.get).spec
  for (modAlias, dependency) in ourSpec.dependencies do
    let spec := (← globalSpecCtx.get)[dependency.name]!.spec
    for proc in spec.procedures do
      let procName := mkIdent <| modAlias ++ proc.name
      -- Since we have lifted the action, we must apply OUR section arguments to
      -- it, rather than the dependency's
      let procTerm <- `(@$procName $(← ourSpec.arguments)*)
      let currMod := (← localSpecCtx.get).stateBaseName.get!
      if (<- getEnv).find? (currMod ++ procName.getId) |>.isSome then
        names := names.push (procName, procTerm)
  pure names


/-- In some cases, during the macro expansion, we need to annotate certain
    arguments with the state type. To get the state type, we need an access to an
    eviorment with we don't have at the macro-expansion stage. To overcome this, we
    introduce the following notation, witch gets resolved to a current state type
    during the elaboration stage  -/
elab "[State]" : term => do
    let stateTpStx ← getStateTpStx
    elabTerm (<- `(term|$stateTpStx)) none

/-- This is used in `require` were we define a predicate over a state.
    Instead of writing `fun st => Pred` this command will pattern match over
    `st` making all its fields accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)
macro "funcases" id:ident t:term : term => `(term| by unhygienic cases $id:ident; exact $t)

abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

structure Vars where
  name : Ident
  type : Term

abbrev VeilM := StateT (Array Vars) TermElabM

/-- Used when first declaring the variables. -/
def getStateDestructorPattern [Monad m] [MonadEnv m] [MonadQuotation m]: m (TSyntax `term) := do
  -- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Pattern.20match.20and.20name.20binder.20.60none.60/near/514568614
  let fields ← (<- getFields).mapM (fun f => return ← `(term|$(mkIdent f)@_)) -- note the @_
  `(term|⟨$fields:term,*⟩)

/-- Used when accessing the state / re-assigning the variables. -/
def getStateAccessorPattern [Monad m] [MonadEnv m] [MonadQuotation m]: m (TSyntax `term) := do
  let fields ← (<- getFields).mapM (fun f => return ← `(term|$(mkIdent f)))
  `(term|⟨$fields:term,*⟩)

mutual
partial def expandDoSeqVeil (stx : doSeq) : VeilM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => return Array.flatten $ ← doS.mapM expandDoElemVeil
  | _ => throwErrorAt stx s!"unexpected syntax of Veil `do`-notation sequence {stx}"

partial def expandDoElemVeil (stx : doSeqItem) : VeilM (Array doSeqItem) := do
  trace[veil.debug] "[expand doElem] {stx}"
  match stx with
  -- Ignore semicolons
  | `(Term.doSeqItem| $stx ;) => expandDoElemVeil $ <- `(Term.doSeqItem| $stx:doElem)
  -- We don't want to introduce state updates after pure statements, so
  -- we pass these through unchanged
  | `(Term.doSeqItem| return $t:term) | `(Term.doSeqItem| pure $t:term)
  | `(Term.doSeqItem| require $t) | `(Term.doSeqItem| assert $t) | `(Term.doSeqItem| assume $t) => return #[stx]
  -- `fresh` also doesn't modify the state, so we pass these through unchanged
  | `(Term.doSeqItem|let $_ : $_ ← fresh $_) | `(Term.doSeqItem|let $_ : $_ ← fresh)
  | `(Term.doSeqItem|let $_ ← fresh $_) | `(Term.doSeqItem|let $_ ← fresh) => return #[stx]
  -- Expand `if` statements
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeqItem* else $els:doSeq) =>
    let fs <- `(Term.doSeqItem| let $h:ident <- fresh)
    let t' <- `(Term.doSeqItem| assume $t)
    let thn := fs :: t' :: thn.toList |>.toArray
    expandDoElemVeil $ <-
      `(Term.doSeqItem| if (∃ $h:ident, $t) then $thn* else $els)
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandDoElemVeil $ <- `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
  -- Expand `if-some` statements
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandDoElemVeil $ <- `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandDoSeqVeil thn
    let els <- expandDoSeqVeil els
    let ret ← `(Term.doSeqItem| if $t then $thn* else $els*)
    return #[ret]
  -- Expand non-deterministic assignments statements
  | `(Term.doSeqItem| $id:ident := *) =>
    let typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
    let fr := mkIdent <| <- mkFreshUserName `fresh
    modify (·.push ⟨fr, typeStx.getD (<- `(_))⟩)
    expandDoElemVeil $ <- `(Term.doSeqItem|$id:ident := $fr)
  | `(Term.doSeqItem| $idts:term := *) =>
    let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
    let typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
    let fr := mkIdent <| <- mkFreshUserName `fresh
    modify (·.push ⟨fr, typeStx.getD (<- `(_))⟩)
    expandDoElemVeil $ <- `(Term.doSeqItem|$idts:term := $fr:ident $ts*)
  -- Expand deterministic assignments statements
  | `(Term.doSeqItem| $id:ident := $t:term) =>
    trace[veil.debug] "[expand assignment to {id.getId}] {stx}"
    let name := id.getId
    let id' <- `(Term.structInstLVal| $id:ident)
    if name.isAtomic then
      let fields <- getFields
      if id.getId ∈ fields then
        throwIfImmutable id'
        -- NOTE: It is very important that we return a single `doSeqItem`;
        -- otherwise syntax highlighting gets broken very badly
        let res ← withRef stx `(Term.doSeqItem| $id:ident ← modifyGet
            (fun st => (($t, {st with $id:ident := $t}))))
        return #[res]
      else
        let res ← `(Term.doSeqItem| $id:ident := $t:term)
        return #[res]
    else -- we are assigning to a structure field (probably a module)
      throwIfImmutable id'
      let base := mkIdent name.getPrefix
      let suff := mkIdent $ name.updatePrefix default
      trace[veil.debug] "assigning to {base.getId} field {suff.getId}"
      expandDoElemVeil $ <- withRef stx `(Term.doSeqItem| $base:ident := { $base with $suff:ident := $t })
  | `(Term.doSeqItem| $idts:term := $t:term) =>
    trace[veil.debug] "[expand assignment with args] {stx}"
    let some (id, ts) := idts.isApp? | return #[stx]
    let stx' <- withRef t `(term| $id[ $[$ts],* ↦ $t:term ])
    let stx <- withRef stx `(Term.doSeqItem| $id:ident := $stx')
    expandDoElemVeil stx
  /-
    To make available the state fields without requiring explicit
    binds, we introduce `let mut field := (<- get).field` for each
    field of state at the beginning of every `do`-block.

    However, this requires us to update these variables after each
    `bind`, to ensure that they have the correct/up-to-date values.
  -/
  -- We handle `bind`s of terms specially, since we want to maintain
  -- the same return value, even though we update the state.
  | `(Term.doSeqItem|$t:term) =>
    let b := mkIdent <| <- mkFreshUserName `_b
    let bind <- `(Term.doSeqItem| let $b:ident ← $t:term)
    return #[bind] ++ (← refreshState) ++ #[← `(Term.doSeqItem| pure $b:ident)]
  -- For everything else, we just update the state afterwards (return
  -- value is `Unit`)
  | doE =>
    trace[veil.debug] "[expand just a doElem] {stx}"
    return #[doE] ++ (← refreshState)
where
refreshState : VeilM (Array doSeqItem) := do
  let pattern ← getStateAccessorPattern
  let refresh ← `(Term.doSeqItem| $pattern:term := ← get)
  return #[refresh]
end

elab (name := VeilDo) "do'" mode:term "in" stx:doSeq : term => do
  /- Array containing all auxilary let-bingings to be inserted in the
    beginning of the `do`-block. It consists of
    - `let mut field := (<- get). field` for each field of the protocol state. We do this
      to be able to access and modify the state fields without the need to use
      `get` and `modify` functions
    - [HACK] `let submodule.act := submodule.act` for each action `act` inherited from
      submodules. As for each submodule, the previous step defines a local variable
      `submodule`, `submodule.act` will be treated as an access to `submodule`'s field `act`,
      rather than an action `act` operation on `submodule`
    - `let freshName <- fresh` for each non-deterministic assigment. We hoist all fresh
      variables to make all the quantifiers top level -/
  let mut preludeAssn : Array doSeqItem := #[]
  let doS <- match stx with
  | `(doSeq| $doE*) => pure doE
  | `(doSeq| { $doE* }) => pure doE
  | _ => throwErrorAt stx "unexpected syntax of Veil `do`-notation sequence {stx}"
  let (doS, vars) <- (expandDoSeqVeil (<- `(doSeq| $doS*))).run #[]
  -- Make available lifted actions using `alias.actionName`
  for a in (← getSubInitializers) ++ (← getSubProcedures) do
    let (actName, actTerm) := a
    preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let $(actName):ident := $(actTerm))
  -- Make available state fields as mutable variables
  let pattern ← getStateDestructorPattern
  preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let mut $pattern:term := (<- get))
  -- We hoist all fresh variables to make all the quantifiers top level
  -- Here we add them to the prelude, as immutable variables
  for v in vars do
    preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let $v.name:ident <- fresh $v.type)
  let doS := preludeAssn.append doS
  trace[veil.debug] "{stx}\n→\n{doS}"
  elabTerm (<- `(term| ((do $doS*) : Wp $mode [State] _))) none

macro_rules
  | `(require $t) => `(Wp.require $t)
  | `(assert  $t) => `(Wp.assert $t)
  | `(assume  $t) => `(Wp.assume $t)
  | `(fresh   $t) => `(Wp.fresh  $t)
  | `(fresh)      => `(Wp.fresh  _)

/- Ensures statement -/

open Tactic in
/-- ```with_rename_old t``` runs tactic `t` and if it introduces any names with `_1` suffix,
    changes this suffix to `_old` -/
elab "with_rename" s:str t:tactic : tactic => withMainContext do
  let hyps <- getLCtx
  withMainContext $ evalTactic t
  withMainContext do
    let hypNews <- getLCtx
    for hyp in hypNews.decls.toArray.reverse do
      if hyp.isSome then
        let hyp := hyp.get!
        unless hyps.findFromUserName? hyp.userName |> Option.isSome do
          let nms := (hyp.userName.toString.splitOn "_")
          let new_name := String.intercalate "_" nms.dropLast ++ s.getString |>.toName
          evalTactic $ <- `(tactic| (revert $(mkIdent hyp.userName):ident; intros $(mkIdent new_name):ident))

/- Expanding `unchanged` statement -/
macro_rules
  | `([unchanged|$s:str| $id:ident]) =>
    let id_old := if s.getString == "'" then mkPrimed id.getId else id.getId.toString ++ s.getString |>.toName
    `($id = $(mkIdent id_old))
  | `([unchanged|$s| $id $ids*]) => `([unchanged|$s| $id] ∧ [unchanged|$s| $ids*])
  | `([unchanged|$_|]) => `(True)

/- One can omit the result variable from [ensures] -/
macro_rules
  | `(requires $pre ensures $post:term $un:unchanged_decl ?) => `(requires $pre ensures (_ : Unit), $post:term $un:unchanged_decl ?)

def getPrePost (spec : doSeq) [Monad m] [MonadError m] [MonadQuotation m] :
  m (Term × TSyntax `rcasesPat × Term) := do
  match spec with
  | `(doSeq| requires $pre ensures $id, $post:term $_:unchanged_decl ?) => pure (pre, id, post)
  | `(doSeq| requires $pre ensures $post:term $_:unchanged_decl ?) => pure (pre, <- `(rcasesPat|(_ : Unit)), post)
  | _ => throwErrorAt spec "Invalid specification: expected `requires ... ensures ...`"

elab_rules : term
  /- if the list of unchanged state fields is omitted, we can restore it by
     checking witch of them are mentioned in the [ensures] body. By default
     we assume that if the state filed is not mentioned, then it is left
     unchanged  -/
  | `(requires $pre ensures $r, $post:term) => do
    let unchangedFields ← getUnchangedFields (fun f => post.raw.find? (·.getId == f) |>.isSome)
    elabTerm (<- `(requires $pre ensures $r, $post:term with unchanged[$[$unchangedFields],*])) none
  | `(requires $pre ensures $r, $post:term with unchanged[$[$ids],*]) => do
    -- withRef t $
    elabTerm (<- `(term| @Wp.spec [State] _ _ (funcases $pre) (
      by rintro st $r st';
         unhygienic cases st';
         with_rename "_old" unhygienic cases st;
         exact $post ∧ [unchanged|"_old"|$ids*]))) none

attribute [actSimp] Bind.bind Pure.pure

/- We need those to simplify `Wp` goals  -/
attribute [ifSimp] ite_self ite_then_self ite_else_self if_true_left
  if_true_right if_false_left if_false_right


end Veil
