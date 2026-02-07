import Lean
import Mathlib.Tactic.ProxyType
import Veil.Util.Meta

open Lean Meta Elab Term Command Deriving

namespace Veil

/-! # Utilities For Instance Derivation -/

section VariousByEquiv

/-! Deriving instances with `Equiv`. -/

variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

def Std.OrientedOrd.by_equiv [inst : Std.OrientedOrd α] : Std.OrientedOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap

def Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := Std.OrientedOrd.by_equiv equiv hmorph |>.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans

def Std.ReflOrd.by_equiv [inst : Std.ReflOrd α] : Std.ReflOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind

def Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := Std.ReflOrd.by_equiv equiv hmorph |>.compare_self
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp

end VariousByEquiv

def sumOrd [Ord α] [Ord β] : Ord (Sum α β) where
  compare
    | Sum.inl a1, Sum.inl a2 => compare a1 a2
    | Sum.inl _,  Sum.inr _  => Ordering.lt
    | Sum.inr _,  Sum.inl _  => Ordering.gt
    | Sum.inr b1, Sum.inr b2 => compare b1 b2

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
  compare_self := by intro a ; cases a <;> simp [sumOrd]

instance [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (Sum α β) where
  eq_swap := by intro a b ; cases a <;> cases b <;> simp [sumOrd] <;> apply Std.OrientedOrd.eq_swap

instance [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (Sum α β) where
  isLE_trans := by intro a b c ; cases a <;> cases b <;> cases c <;> simp [sumOrd] <;> apply Std.TransOrd.isLE_trans

instance [Std.LawfulEqOrd α] [Std.LawfulEqOrd β] : Std.LawfulEqOrd (Sum α β) where
  eq_of_compare := by intro a b ; cases a <;> cases b <;> simp [sumOrd]

end InstancesForSum

end Veil

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

-- NOTE: The following code register `lexOrdForNonDepSigma` and `sumOrd`
-- *to be local instances*. In this case, users don't need to consider
-- which instances to use when writing `deriving`, but this might introduce
-- some unexpected behaviors in other situations.
def mkOrdRelatedInstCmd (className declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← mkHeader ``Ord 0 indVal
    let binders' ← mkInstImplicitBinders className indVal header.argNames
    let localInsts := #[``lexOrdForNonDepSigma, ``sumOrd].map mkCIdent
    `(command|
      attribute [scoped instance] $localInsts* in
      scoped instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* : $(mkCIdent className) ($header.targetType) :=
        $(mkCIdent <| `Veil ++ className ++ `by_equiv)
          (proxy_equiv% $header.targetType)
          (by
            intros
            conv => rhs ; whnf
            simp ($(mkIdent `failIfUnchanged):ident := false) only [$(mkCIdent ``Ordering.then_eq):ident]
            repeat' (first | rfl | destruct_proxy_type | grind)))
  elabVeilCommand cmd
  return true

def mkOrdRelatedInstHandler className := onlyHandleOne (mkOrdRelatedInstCmd className)

def mkStdTransOrdHandler := mkOrdRelatedInstHandler ``Std.TransOrd
def mkStdLawfulEqOrdHandler := mkOrdRelatedInstHandler ``Std.LawfulEqOrd

initialize
  registerDerivingHandler ``Std.TransOrd mkStdTransOrdHandler
  registerDerivingHandler ``Std.LawfulEqOrd mkStdLawfulEqOrdHandler

end DerivingOrdRelatedInstances

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
*named* binders for fields. Also, here does not check whether the
instance binders are type-correct. -/
def mkInstImplicitBindersForFields (className : Name) (indVal : InductiveVal) (argNames : Array Name)
  (fieldNames : Array Name) : TermElabM (Array (Name × Syntax)) := do
  fieldNames.mapIdxM fun i fieldName => do
    let proj ← mkStructureProj indVal argNames fieldName
    let nm ← mkFreshUserName <| Name.mkSimple s!"inst{i}"
    let fieldType ← `(body_type_of_struct_field% ($proj))
    let binder ← `(Lean.Elab.Deriving.instBinderF| [ $(mkIdent nm) : $(mkCIdent className):ident ($fieldType) ])
    pure (nm, binder)
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
  let (localInsts, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``BEq indVal header.argNames fieldNames
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
  let (_, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``DecidableEq indVal header.argNames fieldNames
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
  let (localInsts, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``Hashable indVal header.argNames fieldNames
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
  let (localInsts, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``Inhabited indVal header.argNames fieldNames
  let defaults ← localInsts.mapM fun inst => `(term| $(mkIdent inst).$(mkIdent `default))
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``Inhabited) $(header.targetType) where
    $(mkIdent `default):ident := ⟨$defaults,*⟩)

def mkToJsonInstCmd : CommandElabM Bool := mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``ToJson indVal header.argNames fieldNames
  let (targetNames, targetTypeArgBinders) ← mkTargetTypeArgsBinders 1 header.targetType
  let #[s] := targetNames.map Lean.mkIdent | unreachable!
  let jsonPairs ← fieldNames.zipWithM (bs := localInsts) fun field inst => do
    let fieldStr := toString field
    `(term| ($(Syntax.mkStrLit fieldStr), $(mkIdent inst).$(mkIdent `toJson) $s.$(mkIdent field)))
  let toJsonBody ← `(term| $(mkIdent ``Lean.Json.mkObj) [$[$jsonPairs],*])
  `(command|
  scoped instance $[(priority := $priority?:prio)]? $[$target?:ident]? $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
    $(mkIdent ``ToJson) $(header.targetType) where
    $(mkIdent `toJson):ident $(targetTypeArgBinders.map TSyntax.mk):bracketedBinder* := $toJsonBody)

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
  | _             => throwError "Unsupported class {className}"

end ForStructure

end DerivingInstanceForStructure

end Veil.Deriving
