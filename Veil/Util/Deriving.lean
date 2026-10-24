module

public import Lean
public import Veil.Util.ValueDisplay
public meta import Veil.Util.ProxyType
public meta import Veil.Util.Meta

@[expose] public section

open Lean Meta Elab Term Command Deriving

namespace Veil

/-! # Utilities For Instance Derivation -/

section VariousByEquiv

/-! Deriving instances with `Equiv`. -/

variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

theorem Std.OrientedOrd.by_equiv [inst : Std.OrientedOrd α] : Std.OrientedOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap

theorem Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := Std.OrientedOrd.by_equiv equiv hmorph |>.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans

theorem Std.ReflOrd.by_equiv [inst : Std.ReflOrd α] : Std.ReflOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind

theorem Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := Std.ReflOrd.by_equiv equiv hmorph |>.compare_self
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp

end VariousByEquiv

-- Well, why `PUnit` has no `Ord` instance? Let's just make one
instance : Ord PUnit where
  compare _ _ := Ordering.eq

instance : Std.ReflOrd PUnit where
  compare_self := rfl

instance : Std.OrientedOrd PUnit where
  eq_swap := by intros ; rfl

instance : Std.TransOrd PUnit where
  isLE_trans := by intros ; rfl

instance : Std.LawfulEqOrd PUnit where
  eq_of_compare := by intros ; rfl

@[implicit_reducible]
def sumOrd [Ord α] [Ord β] : Ord (Sum α β) where
  compare
    | Sum.inl a1, Sum.inl a2 => compare a1 a2
    | Sum.inl _,  Sum.inr _  => Ordering.lt
    | Sum.inr _,  Sum.inl _  => Ordering.gt
    | Sum.inr b1, Sum.inr b2 => compare b1 b2

@[implicit_reducible]
def lexOrdForNonDepSigma [Ord α] [Ord β] : Ord ((_ : α) × β) where
  compare x y := lexOrd.compare ⟨x.1, x.2⟩ ⟨y.1, y.2⟩

section InstancesForNonDepSigma

variable {α β} [Ord α] [Ord β]
attribute [local instance] lexOrdForNonDepSigma lexOrd

instance [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd ((_ : α) × β) :=
  Std.OrientedOrd.by_equiv (Equiv.symm (Equiv.sigmaEquivProd α β)) (fun _ _ => rfl)

instance [Std.ReflOrd α] [Std.ReflOrd β] : Std.ReflOrd ((_ : α) × β) :=
  Std.ReflOrd.by_equiv (Equiv.symm (Equiv.sigmaEquivProd α β)) (fun _ _ => rfl)

instance [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd ((_ : α) × β) :=
  Std.TransOrd.by_equiv (Equiv.symm (Equiv.sigmaEquivProd α β)) (fun _ _ => rfl)

instance [Std.LawfulEqOrd α] [Std.LawfulEqOrd β] : Std.LawfulEqOrd ((_ : α) × β) :=
  Std.LawfulEqOrd.by_equiv (Equiv.symm (Equiv.sigmaEquivProd α β)) (fun _ _ => rfl)

end InstancesForNonDepSigma

section InstancesForSum

variable {α β} [Ord α] [Ord β]
attribute [local instance] sumOrd

instance [Std.ReflOrd α] [Std.ReflOrd β] : Std.ReflOrd (Sum α β) where
  compare_self := by intro a ; cases a <;> simp +instances [sumOrd]

instance [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (Sum α β) where
  eq_swap := by intro a b ; cases a <;> cases b <;> simp +instances [sumOrd] <;> apply Std.OrientedOrd.eq_swap

instance [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (Sum α β) where
  isLE_trans := by intro a b c ; cases a <;> cases b <;> cases c <;> simp +instances [sumOrd] <;> apply Std.TransOrd.isLE_trans

instance [Std.LawfulEqOrd α] [Std.LawfulEqOrd β] : Std.LawfulEqOrd (Sum α β) where
  eq_of_compare := by intro a b ; cases a <;> cases b <;> simp +instances [sumOrd]

end InstancesForSum

end Veil

end

public meta section

open Lean Meta Elab Term Command Deriving

namespace Veil.Deriving

/-! # Meta-Programs For Instance Derivation

NOTE: Deriving handlers defined here are not registered if they are for
certain typeclasses that already have builtin handlers (e.g., `BEq`).
This is because (1) there is no explicit way to control which deriving handler
to be used by Lean, and (2) when a deriving handler fails, the derivation
will just fail instead of trying a different handler. Thus, these handlers
are intended to be called via a specialized command `veil_deriving`.
-/

def onlyHandleOne (k : Name → CommandElabM Bool) (declNames : Array Name) : CommandElabM Bool := do
  -- only handle one type at a time
  unless declNames.size = 1 do
    return false
  k declNames[0]!

section DerivingOrdRelatedInstances

open Tactic in
/-- Look at the local context and destruct a hypothesis that is like
the proxy type, including `Sum` and `Sigma`, of some type. -/
local elab "destruct_proxy_type" : tactic => withMainContext do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← whnf decl.type
    if let some nm := ty.getAppFn'.constName? then
      let hyp := decl.userName
      let tac ← match nm with
      | ``Sum => Option.some <$> `(tactic| rcases $(mkIdent hyp):ident with _ | _ )
      | ``Sigma => Option.some <$> `(tactic| rcases $(mkIdent hyp):ident with ⟨_, _⟩ )
      | _ => pure Option.none
      if let some tac := tac then
        evalTactic tac
        return
  throwError "No target proxy type hypothesis found to destruct"

/-- Recursively collect the leaf patterns from a nested `Sum` type into a flat array. -/
partial def collectSumLeaves (ty : Expr) : MetaM (Array (TSyntax `rcasesPat)) := do
  let ty ← whnf ty
  let_expr Sum l r := ty | return #[← `(rcasesPat| _)]
  let left ← collectSumLeaves l
  let right ← collectSumLeaves r
  return left ++ right

/-- Build an `rcasesPatMed` that fully flattens a `Sum` type using alternation. -/
def buildSumPattern (ty : Expr) : MetaM (TSyntax ``Lean.Parser.Tactic.rcasesPatMed) := do
  let leaves ← collectSumLeaves ty
  `(Lean.Parser.Tactic.rcasesPatMed| $leaves:rcasesPat|*)

/-- Recursively build an `rcases` pattern that fully flattens a `Sigma` type in one shot. -/
partial def buildSigmaPattern (ty : Expr) : MetaM (TSyntax `rcasesPat) := do
  let ty ← whnf ty
  let_expr Sigma fst body := ty | return (← `(rcasesPat| _))
  let left ← buildSigmaPattern fst
  let right ← lambdaTelescope body fun _ body => buildSigmaPattern body
  `(rcasesPat| ⟨$left, $right⟩)

open Lean.Parser.Tactic Tactic in
/-- Fully destruct a `Sum`-typed hypothesis using a deep `rcases` pattern. -/
scoped elab "destruct_proxy_sum" : tactic => withMainContext do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← whnf decl.type
    if ty.getAppFn'.isConstOf ``Sum then
      let pat ← buildSumPattern ty
      let hyp := mkIdent decl.userName
      evalTactic (← `(tactic| rcases $hyp:ident with $pat))
      return
  throwError "No Sum-typed hypothesis found to destruct"

open Tactic in
/-- Fully destruct a `Sigma`-typed hypothesis using a deep `rcases` pattern. -/
scoped elab "destruct_proxy_sigma" : tactic => withMainContext do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← whnf decl.type
    if ty.getAppFn'.isConstOf ``Sigma then
      let pat ← buildSigmaPattern ty
      let hyp := mkIdent decl.userName
      evalTactic (← `(tactic| rcases $hyp:ident with $pat))
      return
  throwError "No Sigma-typed hypothesis found to destruct"

-- NOTE: The following code register `lexOrdForNonDepSigma` and `sumOrd`
-- *to be local instances*. In this case, users don't need to consider
-- which instances to use when writing `deriving`, but this might introduce
-- some unexpected behaviors in other situations.

/-- Ensure the homomorphism proof theorem exists for `declName`, creating it if needed.
Returns the theorem name. When both `Std.TransOrd` and `Std.LawfulEqOrd` are derived
for the same type, the second derivation reuses the cached theorem.
Assume `declName` is the fully qualified name. -/
def ensureOrdHomProof (declName : Name) : CommandElabM Name := do
  -- Commands use the source-level namespace, even for a private inductive.
  -- Resolve the generated theorem afterwards to recover its actual private name.
  let thmName := privateToUserName declName ++ `_proxyOrdHom
  if let [(existing, [])] ← resolveGlobalName thmName then
    return existing
  let indVal ← getConstInfoInduct declName
  -- Compute a name relative to the current namespace so that
  -- `elabVeilCommand` (which uses the current namespace) doesn't double it.
  let currNs ← getCurrNamespace
  let relThmName := thmName.replacePrefix currNs .anonymous
  let cmd ← liftTermElabM do
    let header ← mkHeader ``Ord 0 indVal
    let localInsts := #[``lexOrdForNonDepSigma, ``sumOrd].map mkCIdent
    let a1 ← mkIdent <$> mkFreshUserName `a1
    let a2 ← mkIdent <$> mkFreshUserName `a2
    `(command|
      attribute [scoped instance] $localInsts* in
      theorem $(mkIdent relThmName) $header.binders:bracketedBinder* :
        ∀ $a1:ident $a2:ident,
          compare $a1:ident $a2:ident = compare ((veil_proxy_equiv% $header.targetType) $a1:ident) ((veil_proxy_equiv% $header.targetType) $a2:ident) := by
            intros
            conv => rhs ; whnf
            simp ($(mkIdent `failIfUnchanged):ident := false) only [$(mkCIdent ``Ordering.then_eq):ident]
            try (destruct_proxy_sum <;> destruct_proxy_sum <;> try rfl)
            all_goals (first | rfl | (destruct_proxy_sigma ; first | rfl | grind)))
  elabVeilCommand cmd
  resolveGlobalConstNoOverloadCore thmName

def mkOrdRelatedInstCmd (className declName : Name) : CommandElabM Bool := do
  let thmName ← ensureOrdHomProof declName
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← mkHeader ``Ord 0 indVal
    let binders' ← mkInstImplicitBinders className indVal header.argNames
    let localInsts := #[``lexOrdForNonDepSigma, ``sumOrd].map mkCIdent
    `(command|
      attribute [scoped instance] $localInsts* in
      scoped instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* : $(mkCIdent className) ($header.targetType) :=
        $(mkCIdent <| `Veil ++ className ++ `by_equiv)
          (veil_proxy_equiv% $header.targetType)
          $(mkCIdent thmName))
  elabVeilCommand cmd
  return true

def mkOrdRelatedInstHandler className := onlyHandleOne (mkOrdRelatedInstCmd className)

def mkStdTransOrdHandler := mkOrdRelatedInstHandler ``Std.TransOrd
def mkStdLawfulEqOrdHandler := mkOrdRelatedInstHandler ``Std.LawfulEqOrd

initialize
  registerDerivingHandler ``Std.TransOrd mkStdTransOrdHandler
  registerDerivingHandler ``Std.LawfulEqOrd mkStdLawfulEqOrdHandler

end DerivingOrdRelatedInstances

section DerivingDisplay

open Lean.Parser.Term in
/-- `Display` for a non-recursive inductive type without indices, such as a module's `Label`, in the
shape of its derived `ToJson`: `"c"` for a constructor without arguments, `{"c": {"x": …}}` for one
with named arguments, with each argument shown by its `Display`.

Each type parameter needs `Repr` besides `Display`: an argument whose type has no structured
`Display`, such as `Option α`, falls back to its `Repr`, which needs `Repr α`. Without the binder,
`reprOfUnrepresentable` would silently supply it. -/
def mkDisplayInstCmdForInductive (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  if indVal.isRec || indVal.numIndices != 0 || isStructure (← getEnv) declName then
    throwError "deriving `Display` is supported for non-recursive inductive types without indices, \
      other than structures: {declName}"
  let cmd ← liftTermElabM do
    let hole ← `(term| _)
    let header ← mkHeader ``Display 0 indVal
    let reprBinders ← mkInstImplicitBinders ``Repr indVal header.argNames
    let x ← mkIdent <$> mkFreshUserName `x
    -- One alternative per constructor, e.g. for `| send (n m : node)` of `Label node`:
    --   `| @Label.send _ a₁ a₂ => {"send": {"n": display a₁, "m": display a₂}}`
    let alts : Array (TSyntax ``matchAlt) ← indVal.ctors.toArray.mapM fun ctorName => do
      let ctorInfo ← getConstInfoCtor ctorName
      forallTelescopeReducing ctorInfo.type fun xs _ => do
        -- A fresh pattern variable for each argument of the constructor (the binders after the
        -- type's parameters), and the argument's name as written, if it has one.
        let mut args : Array Ident := #[]
        let mut names : Array StrLit := #[]
        for i in [:ctorInfo.numFields] do
          let decl ← xs[indVal.numParams + i]!.fvarId!.getDecl
          -- As in `ToJson`, use macro scopes as a heuristic for unnamed arguments. This is
          -- only a convention: macros can introduce named binders with scopes, and generated
          -- names need not have scopes, so this does not reliably distinguish the two.
          unless decl.userName.hasMacroScopes do
            if let .str _ s := decl.userName then
              names := names.push (Syntax.mkStrLit s)
          args := args.push (mkIdent (← mkFreshUserName `a))
        -- The type's parameters are inaccessible in the pattern: `_` for each.
        let params := Array.replicate indVal.numParams hole
        let .str _ s := ctorName.eraseMacroScopes
          | throwError "unsupported constructor name: {ctorName}"
        let ctorStr := Syntax.mkStrLit s
        let vals ← args.mapM fun a => `($(mkCIdent ``Display.display) $a)
        -- The JSON of the constructor, shaped as the derived `ToJson` shapes it:
        -- `"c"` without arguments, `{"c": {"x": …, …}}` if every argument has a name, otherwise
        -- `{"c": …}` for one argument and `{"c": [… , …]}` for several.
        let rhs ← if args.isEmpty then
            `($(mkCIdent ``Lean.Json.str) $ctorStr)
          else if names.size == args.size then
            let fields ← (names.zip vals).mapM fun (n, v) => `(($n, $v))
            `($(mkCIdent ``Lean.Json.mkObj) [($ctorStr, $(mkCIdent ``Lean.Json.mkObj) [$fields,*])])
          else match vals with
            | #[v] => `($(mkCIdent ``Lean.Json.mkObj) [($ctorStr, $v)])
            | _ => `($(mkCIdent ``Lean.Json.mkObj) [($ctorStr, $(mkCIdent ``Lean.Json.arr) #[$vals,*])])
        `(matchAltExpr| | @$(mkCIdent ctorName):ident $params* $args* => $rhs)
    `(command|
      instance $header.binders:bracketedBinder* $(reprBinders.map TSyntax.mk):bracketedBinder* :
          $(mkCIdent ``Display) $header.targetType where
        display $x:ident := match $x:ident with $alts:matchAlt*)
  elabVeilCommand cmd
  return true

def mkDisplayHandler := onlyHandleOne mkDisplayInstCmdForInductive

initialize registerDerivingHandler ``Display mkDisplayHandler

end DerivingDisplay

section DerivingInstanceForStructure

/-!
Utilities for deriving instances for structures by assuming
instances for their fields.
-/

/-- Similar to `type_of%`, but returns the body type of a `∀`-type
after stripping exactly one forall binder (the structure argument).
Throws an error if the body type has loose bound variables. -/
elab "body_type_of_struct_field% " t:term : term => do
  let e ← elabTerm t none
  let type ← inferType e
  let type := type.consumeMData
  let .forallE _ _ body _ := type
    | throwError "Expected a ∀-type, got {type}"
  if body.hasLooseBVars then
    throwError "The body type of {t} has loose bound variables"
  return body

open TSyntax.Compat in
/-- Similar to `Lean.Elab.Deriving.mkHeader`, but does not add implicit
binders for a typeclass or arguments of `targetType` into the header. -/
def mkHeaderWithoutInstImplicitBinders (indVal : InductiveVal) : TermElabM Header := do
  let argNames      ← mkInductArgNames indVal
  let binders       ← mkImplicitBinders argNames
  let targetType    ← mkInductiveApp indVal argNames
  return {
    binders     := binders
    argNames    := argNames
    targetNames := #[]
    targetType  := targetType
  }

private def mkTargetTypeArgsBinders (arity : Nat) (targetType : Term) :
  CoreM (Array Name × Array (TSyntax ``Lean.Elab.Deriving.explicitBinderF)) := do
  let mut targetNames := #[]
  for _ in *...arity do
    targetNames := targetNames.push (← mkFreshUserName `x)
  let binders ← targetNames.mapM fun targetName => `(Lean.Elab.Deriving.explicitBinderF| ($(mkIdent targetName) : $targetType))
  pure (targetNames, binders)

/-- Similar to `Lean.Elab.Deriving.mkInstImplicitBinders`, but produces
*named* binders for fields. Definitionally equal field types share one
instance binder; the first field's instance name is returned for every
later occurrence. -/
def mkInstImplicitBindersForFields (className : Name) (indVal : InductiveVal) (argNames : Array Name)
  (fieldNames : Array Name) : TermElabM (Array Name × Array Syntax) := do
  -- Attach a fresh instance name to every field before canonicalizing, so
  -- `representatives` directly maps each field to the instance name of its
  -- first definitionally equal occurrence.
  let fields ← fieldNames.mapIdxM fun i fieldName =>
    return (fieldName, ← mkFreshUserName <| Name.mkSimple s!"inst{i}")
  let canonicalized ← forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let structType := mkAppN (mkConst indVal.name <| indVal.levelParams.map mkLevelParam) params
    withLocalDeclD `s structType fun s =>
      canonicalizeByDefEqType fields fun (fieldName, _) => do
        inferType (← mkProjection s fieldName)
  let binders ← canonicalized.unique.mapM fun (fieldName, instName) => do
    let fieldType ← `(body_type_of_struct_field% ($(← mkStructureProj indVal argNames fieldName)))
    `(Lean.Elab.Deriving.instBinderF| [ $(mkIdent instName) : $(mkCIdent className):ident ($fieldType) ])
  return (canonicalized.representatives.map (·.2), binders.map (·.raw))
where
 -- similar to `mkInductiveApp`, but produces a projection of a field
 mkStructureProj (indVal : InductiveVal) (argNames : Array Name) (fieldName : Name) : TermElabM Term :=
  let field := mkCIdent (indVal.name ++ fieldName)
  let args  := argNames.map mkIdent
  -- let field := mkIdent fieldName
  `(@$field $args*)

namespace ForStructure

def mkInstCmdTemplate (declName : Name)
  (k : StructureInfo → InductiveVal → Header → TermElabM Command) : CommandElabM Bool := do
  let env ← getEnv
  let declName ← resolveGlobalConstNoOverloadCore declName
  let some info := getStructureInfo? env declName
    | return false
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← mkHeaderWithoutInstImplicitBinders indVal
    k info indVal header
  elabVeilCommand cmd
  return true

section

variable (declName : Name) (target? : Option Ident) (priority? : Option (TSyntax `prio))

-- FIXME: How to configure scoped vs non-scoped instances?

def mkBEqInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← mkInstImplicitBindersForFields ``BEq indVal header.argNames fieldNames
  let (targetNames, targetTypeArgBinders) ← mkTargetTypeArgsBinders 2 header.targetType
  let #[s1, s2] := targetNames.map Lean.mkIdent | unreachable!
  let beqTerms ← fieldNames.zipWithM (bs := localInsts) fun field inst => `(term| $(mkIdent inst).$(mkIdent `beq) $s1.$(mkIdent field) $s2.$(mkIdent field))
  let beqBody ← repeatedOp ``Bool.and beqTerms (default := ← `(term| true))
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``BEq) $(header.targetType) where
    $(mkIdent `beq):ident $(targetTypeArgBinders.map TSyntax.mk):bracketedBinder* := $beqBody)

def mkDecidableEqInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (_, binders') ← mkInstImplicitBindersForFields ``DecidableEq indVal header.argNames fieldNames
  let (targetNames, targetTypeArgBinders) ← mkTargetTypeArgsBinders 2 header.targetType
  let #[s1, s2] := targetNames.map Lean.mkIdent | unreachable!
  -- Build the conjunction: s1.field1 = s2.field1 ∧ s1.field2 = s2.field2 ∧ ...
  let eqTerms ← fieldNames.mapM fun field => `(term| $s1.$(mkIdent field) = $s2.$(mkIdent field))
  let eqBody ← repeatedAnd eqTerms
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``DecidableEq) $(header.targetType) :=
    fun $(targetTypeArgBinders.map TSyntax.mk)* =>
    $(mkIdent ``decidable_of_iff) $eqBody (by cases $s1:ident; cases $s2:ident; grind))

def mkHashableInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← mkInstImplicitBindersForFields ``Hashable indVal header.argNames fieldNames
  let (targetNames, targetTypeArgBinders) ← mkTargetTypeArgsBinders 1 header.targetType
  let #[s] := targetNames.map Lean.mkIdent | unreachable!
  -- Build the hash body: (hash s.field1) |> mixHash (hash s.field2) |> ...
  let hashBody ← match fieldNames.toList with
    | [] => `(term| 0)
    | f :: fs =>
      let inst1 :: localInsts := localInsts.toList | unreachable!
      let first ← `(term| $(mkIdent inst1).$(mkIdent `hash) ($s.$(mkIdent f)))
      fs.zip localInsts |>.foldlM (init := first) fun acc (field, inst) => do
        `(term| $acc |> $(mkIdent ``mixHash) ($(mkIdent inst).$(mkIdent `hash) ($s.$(mkIdent field))))
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``Hashable) $(header.targetType) where
    $(mkIdent `hash):ident $(targetTypeArgBinders.map TSyntax.mk):bracketedBinder* := $hashBody)

def mkInhabitedInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← mkInstImplicitBindersForFields ``Inhabited indVal header.argNames fieldNames
  let defaults ← localInsts.mapM fun inst => `(term| $(mkIdent inst).$(mkIdent `default))
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``Inhabited) $(header.targetType) where
    $(mkIdent `default):ident := ⟨$defaults,*⟩)

private def mkJsonObjectInstCmd (className methodName : Name) : CommandElabM Bool :=
    mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← mkInstImplicitBindersForFields className indVal header.argNames fieldNames
  let (targetNames, targetTypeArgBinders) ← mkTargetTypeArgsBinders 1 header.targetType
  let #[s] := targetNames.map Lean.mkIdent | unreachable!
  let jsonPairs ← fieldNames.zipWithM (bs := localInsts) fun field inst => do
    let fieldStr := toString field
    `(term| ($(Syntax.mkStrLit fieldStr), $(mkIdent inst).$(mkIdent methodName) $s.$(mkIdent field)))
  let jsonBody ← `(term| $(mkIdent ``Lean.Json.mkObj) [$[$jsonPairs],*])
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent className) $(header.targetType) where
    $(mkIdent methodName):ident $(targetTypeArgBinders.map TSyntax.mk):bracketedBinder* := $jsonBody)

def mkToJsonInstCmd : CommandElabM Bool :=
  mkJsonObjectInstCmd declName target? priority? ``ToJson `toJson

/-- `Display` for a structure such as a module's state or theory: the object of its fields, as
`mkToJsonInstCmd` builds it, with each field shown by its `Display`. -/
def mkDisplayInstCmd : CommandElabM Bool :=
  mkJsonObjectInstCmd declName target? priority? ``Display `display

def mkReprInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← mkInstImplicitBindersForFields ``Repr indVal header.argNames fieldNames
  let s ← mkIdent <$> mkFreshUserName `s
  let n ← mkIdent <$> mkFreshUserName `n
  let embeddedStringStx (x : String) : TSyntax `str :=
    { raw := Lean.Syntax.node Lean.SourceInfo.none `str #[Lean.Syntax.atom Lean.SourceInfo.none ("\"" ++ x ++ " := \"")] }
  let fieldReprs ← fieldNames.zipWithM (bs := localInsts) fun field inst => do
    `(term| $(mkIdent ``Std.Format.append) $(embeddedStringStx <| toString field)
      ($(mkIdent inst).$(mkIdent `reprPrec) ($s.$(mkIdent field)) $n))
  let fieldsFormat ← if fieldReprs.isEmpty then `(term| "") else `(term| $(mkIdent ``Std.Format.joinSep) [$fieldReprs,*] ", ")
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``Repr) $(header.targetType) where
    $(mkIdent `reprPrec):ident $s:ident $n:ident := $(mkIdent ``Std.Format.bracket) "{ " $fieldsFormat " }")

end

syntax "veil_deriving " ident "for" ident ("with_name" ident)? ("with_priority" prio)? : command

elab_rules : command
| `(veil_deriving $idt:ident for $decl:ident $[with_name $target?:ident]? $[with_priority $priority?:prio]?) => do
  let declName := decl.getId
  let className ← resolveGlobalConstNoOverload idt
  let _ ← match className with
  | ``BEq         => mkBEqInstCmd declName target? priority?
  | ``DecidableEq => mkDecidableEqInstCmd declName target? priority?
  | ``Hashable    => mkHashableInstCmd declName target? priority?
  | ``Inhabited   => mkInhabitedInstCmd declName target? priority?
  | ``ToJson      => mkToJsonInstCmd declName target? priority?
  | ``Display     => mkDisplayInstCmd declName target? priority?
  | ``Repr        => mkReprInstCmd declName target? priority?
  | _             => throwError "Unsupported class {className}"

end ForStructure

/-! # Deriving Wrapper Instances for Single-Payload Structures -/

syntax "veil_derive_wrapper_instances " ident : command

elab_rules : command
| `(veil_derive_wrapper_instances $decl:ident) => do
  let ok ← ForStructure.mkInstCmdTemplate decl.getId fun info indVal header => do
    let fields ← forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
      let ty := mkAppN (mkConst indVal.name (indVal.levelParams.map mkLevelParam)) params
      withLocalDeclD `s ty fun s =>
        info.fieldNames.filterM fun field => do
          return !(← isProp (← inferType (← mkProjection s field)))
    let #[field] := fields
      | throwError "Expected a structure with exactly one non-proof field"
    let args : Array Term := header.argNames.map (fun n => ⟨(mkIdent n).raw⟩)
    let storage ← `(body_type_of_struct_field% (@$(mkCIdent (indVal.name ++ field)) $args*))
    let f := mkIdent field
    let t := header.targetType
    let bs := header.binders
    -- Use storage constraints: builtin deriving also constrains phantom parameters,
    -- and deriving `BEq` for dependent proof fields requires `LawfulBEq`.
    -- Reuse some Lean's deriving tactics for the equality laws below.
    -- Use ordinary instances so callers do not need to open the wrapper namespace.
    let cmds := #[
      ← `(command| instance $bs:bracketedBinder* [BEq $storage] : BEq $t where
        beq a b := a.$f == b.$f),
      ← `(command| instance $bs:bracketedBinder* [Hashable $storage] : Hashable $t where
        hash a := hash a.$f),
      ← `(command| instance $bs:bracketedBinder* [DecidableEq $storage] : DecidableEq $t :=
        fun a b => decidable_of_iff (a.$f = b.$f) (by
          constructor
          · intro h; cases a; cases b; cases h; rfl
          · intro h; cases h; rfl)),
      ← `(command| instance $bs:bracketedBinder* [BEq $storage] [ReflBEq $storage] : ReflBEq $t where
        rfl := by
          dsimp only [BEq.beq]
          deriving_ReflEq_tactic),
      ← `(command| instance $bs:bracketedBinder* [BEq $storage] [EquivBEq $storage] : EquivBEq $t where
        rfl {a} := beq_self_eq_true a.$f
        symm {a b} h := BEq.symm (α := $storage) h
        trans {a b c} h₁ h₂ := BEq.trans (α := $storage) h₁ h₂),
      ← `(command| instance $bs:bracketedBinder* [BEq $storage] [LawfulBEq $storage] : LawfulBEq $t :=
        LawfulBEq.mk (by
          dsimp only [BEq.beq]
          deriving_LawfulEq_tactic)),
      ← `(command| instance $bs:bracketedBinder* [BEq $storage] [Hashable $storage]
          [LawfulHashable $storage] : LawfulHashable $t where
        hash_eq a b := LawfulHashable.hash_eq a.$f b.$f),
      ← `(command| instance $bs:bracketedBinder* [Ord $storage] : Ord $t where
        compare a b := compare a.$f b.$f),
      ← `(command| instance $bs:bracketedBinder* [Ord $storage] [Std.ReflOrd $storage] : Std.ReflOrd $t where
        compare_self {a} := Std.ReflOrd.compare_self (a := a.$f)),
      ← `(command| instance $bs:bracketedBinder* [Ord $storage] [Std.OrientedOrd $storage] : Std.OrientedOrd $t where
        eq_swap {a b} := Std.OrientedOrd.eq_swap (a := a.$f) (b := b.$f)),
      ← `(command| instance $bs:bracketedBinder* [Ord $storage] [Std.TransOrd $storage] : Std.TransOrd $t where
        isLE_trans {a b c} := Std.TransOrd.isLE_trans (a := a.$f) (b := b.$f) (c := c.$f)),
      ← `(command| instance $bs:bracketedBinder* [Ord $storage] [Std.LawfulEqOrd $storage] : Std.LawfulEqOrd $t where
        eq_of_compare {a b} h := by
          have h : a.$f = b.$f := Std.LawfulEqOrd.eq_of_compare h
          cases a; cases b; cases h; rfl)
    ]
    -- `mkNullNode` bundles multiple commands into a single syntax node;
    -- command elaboration processes its children in order.
    return ⟨mkNullNode (cmds.map (·.raw))⟩
  unless ok do throwError "Expected a structure"

end DerivingInstanceForStructure

end Veil.Deriving
