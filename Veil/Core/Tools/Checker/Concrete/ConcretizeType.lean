import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.State

import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType

import Veil.Util.Meta

import Lean.Parser.Term
open Lean Elab Command Veil


namespace Lean
/-- `t_isEnum` is an instance, where `t` is declared as an `enum` type. -/
def Name.toEnumInst (name : Name) : Name := name.appendAfter "_isEnum"

/-- `t_Enum` is a type class. -/
def Name.toEnumClass (name : Name) : Name := name.appendAfter "_Enum"

/-- Given a name `t`, return the name of its instance like `instPrefix_t`. -/
def Name.toInstName (name : Name) (instPrefix : String) : Name := name.appendBefore instPrefix
end Lean


/- TODO: Go through `import Veil.Frontend.DSL.Module.Util`, I believe there are more utility functions that can be used here -/
/- Collect all the mutable state fields. Without this step, may lead to `none` field name from `immutable` field. -/
def Veil.Module.stateFieldNames [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array Name) := do
  let sc := mod.mutableComponents
  return sc.map (·.name)


/- Collect all the mutable state fields of the given kind. -/
def Veil.Module.fieldNames [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (kind : StateComponentKind)
  : m (Array Name) := do
  let sc := mod.mutableComponents |>.filter (·.kind == kind)
  return sc.map (·.name)


/-- When a type is declared using `enum`, it will first elaborated to a typeclass,
then elaborated to syntax `instantiate _isEnum` and added into the `parameters`
field of `Veil.Module` with name postfix `_isEnum`.
Refer `Module.declareUninterpretedSort` for details.

The function collects all the type idents that are either enum types or non-enum
types based on the `isEnum` flag.
-/
def Veil.Module.typeIdents [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (isEnum : Bool)
  : m (Array (TSyntax `ident)) := do
  let paramNames : Array Name := mod.parameters.map (·.name)
  let isEnumType :=
    fun t => paramNames.contains (t.getId.toEnumInst) -- to a function
  let pred := if isEnum then isEnumType else fun t => not (isEnumType t)
  let ids ← mod.sortIdents
  return ids.filter pred


/-- Given name of instance like `Ord`, return all the instance binders for all the types. -/
def Veil.Module.instBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (instName : Name)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let instNamePostfix := match instName with
    | ``Ord       => "_ord"
    | ``FinEnum   => "_fin_enum"
    | ``Hashable  => "_hash"
    | ``ToJson    => "_to_json"
    | _ => "_anonymous_inst"
  let ids : Array Ident ← mod.sortIdents
  ids.mapM (fun t : Ident =>
    let name' := t.getId.appendAfter instNamePostfix
    do `(bracketedBinder| [$(mkIdent name') : $(mkIdent instName) $t]) )


/-- Generate propCmp (e.g., `transCmp`, `LawfulEqCmp`) binder for a given type.
[Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
-/
def Veil.propCmpBinder [Monad m] [MonadQuotation m] [MonadError m] (propName : Name) (sortIdent : Ident)
  : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let instNamePostfix := match propName with
    | ``Std.TransCmp     => "_trans_cmp"
    | ``Std.LawfulEqCmp   => "_lawful_cmp"
    | _ => "_anonymous_prop_cmp"
    let name' := sortIdent.getId.appendAfter instNamePostfix
  `(bracketedBinder| [$(mkIdent name') : $(mkIdent propName) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sortIdent) ))])


/-- Different from `Module.getStateBinders`, which used to collect Codomain and Domain.
* `res` is the `Domain`, while `base` is the `Codomain`/type of return value.
* For individual, base is always `#[]`.
* For relation, base is always `Bool`.
-/
def Veil.Module.getStateDomains [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) : m (Array (Name × Array Term)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable =>
      let (res, base) ← splitForallArgsCodomain (← sc.typeStx)
      match sc.kind with
      | .individual =>  return .some (sc.name, #[base])
      | .function   =>  return .some (sc.name, res.append #[base])
      | .relation   =>  return .some (sc.name, res)
      | _           =>  return .none
    | _ => return .none


-- let param : Parameter := { kind := .uninterpretedSort, name := name, «type» := typeT, userSyntax := userStx }
-- let dec_eq : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
-- let inhabited : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
def Veil.Module.collectVeilVarsBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Std.HashMap Name (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.parameters.foldlM (init := {}) fun acc p => do
    let b ← p.binder
    pure <| acc.insert p.name b


def lookupBindersWithSuffix [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (suf? : Option String) (errHead : String)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let typeIdents : Array (TSyntax `ident) ← mod.sortIdents
  let varsBinders ← mod.collectVeilVarsBinders
  typeIdents.mapM fun t : (TSyntax `ident) => do
    let base := t.getId
    let key  := match suf? with
                | none      => base
                | some suf  => base.appendAfter suf
    match varsBinders.get? key with
    | some b => pure b
    | none   => throwError m!"{errHead} for type {t}"


def Veil.Module.typeExplicitBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod none "No type binder found"

def Veil.Module.typeDecEqBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
: m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod (some "_dec_eq") "No DecidableEq binder found"

def Veil.Module.typeInhabitedBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod (some "_inhabited") "No Inhabited binder found"



/-- Code from Qiyuan. Generate inductive type and instances for `enum` typeclass. -/
def deriveEnumInstance (name : Name) : CommandElabM Unit := do
  let clsName ← resolveGlobalConstNoOverloadCore name.toEnumClass
  let .some info := getStructureInfo? (← getEnv) clsName | throwError "no such structure {clsName}"
  -- NOTE: assume the last two are the propositions to satisfy
  let fields := info.fieldNames.pop.pop
  trace[veil.debug] "info.fieldName: {info.fieldNames}"
  let ctors : Array (TSyntax ``Lean.Parser.Command.ctor) ←
    fields.mapM fun fn => `(Lean.Parser.Command.ctor| | $(mkIdent fn):ident )
  trace[veil.debug] "fields: {fields}"
  let defineIndTypeCmd ← do
    if ctors.size > 0 then
      `(inductive $(mkIdent name) where $[$ctors]* deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr), $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
    else
      `(inductive $(mkIdent name) where deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr))
  let instClauses ←
    fields.mapM fun fn => `(Lean.Parser.Term.structInstField| $(mkIdent fn):ident := $(mkIdent <| name ++ fn):ident )
  let completeRequirement := info.fieldNames.back!
  let distinctRequirement := info.fieldNames.pop.back!
  let proof1 ← `(Lean.Parser.Term.structInstField| $(mkIdent distinctRequirement):ident := (by (first | decide | grind)) )
  let proof2 ← do
    let x := mkIdent `x
    `(Lean.Parser.Term.structInstField| $(mkIdent completeRequirement):ident := (by intro $x:ident ; cases $x:ident <;> (first | decide | grind)) )
  let instClauses := instClauses.push proof1 |>.push proof2
  let instantiateCmd ←
    `(instance : $(mkIdent clsName) $(mkIdent name) where $[$instClauses]*)
  let allConstructors ← do
    let arr := fields.map fun fn => (mkIdent <| name ++ fn)
    `(term| [ $arr,* ] )
  let instantiateFinEnumCmd ←
    `(instance : $(mkIdent ``FinEnum) $(mkIdent name) :=
      $(mkIdent ``FinEnum.ofList) $allConstructors (by simp ; exact $(mkIdent <| clsName ++ completeRequirement)))
  elabCommand defineIndTypeCmd
  trace[veil.debug] "defineIndTypeCmd: {defineIndTypeCmd}"
  elabCommand instantiateCmd
  trace[veil.debug] "instantiateCmd: {instantiateCmd}"
  elabCommand instantiateFinEnumCmd
  trace[veil.debug] "instantiateFinEnumCmd: {instantiateFinEnumCmd}"



-- instance instOrdpc_state : Ord pc_state where
--   compare s1 s2 :=
--     compare (s1.toCtorIdx) (s2.toCtorIdx)
-- instance : Hashable pc_state where
--   hash s := hash s!"pc_state{repr s.toCtorIdx}"
def deriveEnumOrdHashable (name : Name) : CommandElabM Unit := do
  -- let clsName ← resolveGlobalConstNoOverloadCore name
  let ordInst ← `(command|
    instance $(mkIdent <| Name.appendBefore name "instOrd"):ident : $(mkIdent ``Ord) $(mkIdent name) where
      $(mkIdent `compare):ident $(mkIdent `s1):ident $(mkIdent `s2):ident :=
        $(mkIdent ``compare) $(mkIdent `s1.toCtorIdx) $(mkIdent `s2.toCtorIdx))
  dbg_trace "ordInst: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic ordInst}"
  elabVeilCommand ordInst

  let hashableInst ← `(command|
    instance $(mkIdent <| Name.appendBefore name "instHashable"):ident : $(mkIdent ``Hashable) $(mkIdent name) where
      $(mkIdent `hash):ident $(mkIdent `s):ident :=
        $(mkIdent ``hash) $(mkIdent `s.toCtorIdx))

  dbg_trace "hashableInst: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic hashableInst}"
  elabVeilCommand hashableInst

elab "deriving_ord_hashable_for_enum " name:ident : command => do
  let name := name.getId
  deriveEnumOrdHashable name

-- instance :  Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
--   apply Std.OrientedCmp.mk
--   unfold compare inferInstanceAs instOrdPc_state
--   intro a b; cases a <;>
--     cases b <;> rfl
-- instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
--   apply Std.TransCmp.mk
--   unfold compare inferInstanceAs instOrdPc_state
--   decide
-- instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))):= by
--   apply Std.LawfulEqCmp.mk
--   unfold compare inferInstanceAs instOrdPc_state
--   intro a b; cases a <;>
--     cases b <;> simp
def deriveEnumPropCmpInsts (name : Name) : CommandElabM Unit := do
  let orientedCmp ← `(command|
    instance : $(mkIdent ``Std.OrientedCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.OrientedCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      intro $(mkIdent `a) $(mkIdent `b); cases $(mkIdent `a):ident <;>
        cases $(mkIdent `b):ident <;> rfl)
  dbg_trace "orientedCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic orientedCmp}"
  elabVeilCommand orientedCmp

  let transCmp ← `(command|
    instance : $(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.TransCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      decide)
  dbg_trace "transCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic transCmp}"
  elabVeilCommand transCmp

  let lawfulCmp ← `(command|
    instance : $(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.LawfulEqCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      intro $(mkIdent `a) $(mkIdent `b); cases $(mkIdent `a):ident <;>
        cases $(mkIdent `b):ident <;> simp)
  dbg_trace "lawfulCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lawfulCmp}"
  elabVeilCommand lawfulCmp


syntax (name := deriveEnumInsts) "deriving_Enum_Insts" : command

@[command_elab deriveEnumInsts]
def elabDeriveEnumInsts : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_Enum_Insts) =>
    let mod ← getCurrentModule
    let enumTypeIdents ← mod.typeIdents (isEnum := true)
    for t in enumTypeIdents do
      let name := t.getId
      dbg_trace s!"Processing enum type: {name}"
      deriveEnumInstance name
      deriveEnumOrdHashable name
      deriveEnumPropCmpInsts name
  | _ => throwError "unrecognized command {stx}"



elab "deriving_propCmp_for_enum" name:ident : command => do
  let name := name.getId
  deriveEnumPropCmpInsts name


-- attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] instFinEnumForToDomain in
-- #specialize_nextact with FieldConcreteType
--   injection_begin
--     [FinEnum process]
--     [Hashable process]
--     [Ord process]
--     [FinEnum states]
--     [Hashable states]
--     [Ord states]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]

--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     -- [Ord (process × states)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--     -- [Ord (process × process)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--   injection_end => NextAct'
def mkProdFromArray (xs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  match xs.toList with
  | []      =>  `(term| Unit)
  | [t]     =>  return ←`(term | ($t))
  | t :: ts =>  ts.foldlM (init := t) fun acc b => `(term| ($acc × ($b)))

syntax (name := genExecutableNextAct) "gen_executable_NextAct" : command

def genExecutableList (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let mut binders := finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts

  -- let stateDomains ← mod.getStateDomains
  -- for (_, doms) in stateDomains do
  --   let productDomain ← mkProdFromArray doms |> liftTermElabM
  --   let lawfulInst ← `(bracketedBinder| [$(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   let transInst ← `(bracketedBinder| [$(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   binders := binders.push lawfulInst
  --   binders := binders.push transInst

  return ← `(command |
    #gen_executable_list! log_entry_being $(mkIdent ``Std.Format)
    targeting $(mkIdent `NextAct')
    injection_begin
      $[$binders]*
    injection_end)

@[command_elab genExecutableNextAct]
def elabGenExecutableNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let instCmd ← genExecutableList mod
  dbg_trace "{← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd

syntax (name := genNextActCommand) "gen_NextAct" : command

def genNextAct' (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let mut binders := finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts

  -- let stateDomains ← mod.getStateDomains
  -- for (_, doms) in stateDomains do
  --   let productDomain ← mkProdFromArray doms |> liftTermElabM
  --   let lawfulInst ← `(bracketedBinder| [$(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   let transInst ← `(bracketedBinder| [$(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   binders := binders.push lawfulInst
  --   binders := binders.push transInst

  return ← `(command |
      attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $(mkIdent `instFinEnumForToDomain) in
      #specialize_nextact with $(mkIdent `FieldConcreteType)
      injection_begin
      $[$binders]
      *
      injection_end => $(mkIdent `NextAct'))


@[command_elab genNextActCommand]
def elabGenNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let instCmd ← genNextAct' mod
  dbg_trace "{← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd

-- TSyntax `term

#check inferInstanceAs (BEq (TSyntax `term))


-- instance lawful
--   [FinEnum process]
--   [Ord process]
--   [FinEnum states]
--   [Ord states]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states ))))]
-- -- variable [Ord (process × process)]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process ))))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
-- -- variable [Ord (process × List process)]
--   -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]

--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
--   (f : State.Label)
--   : Veil.LawfulFieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f)
--   ((⌞? instRepForFieldRepresentation ⌟) f) :=
-- by
--   cases f <;>
--   first
--   | (dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, instRepForFieldRepresentation, id]; infer_instance)
--   | (exact Veil.instFinsetLikeLawfulFieldRep (Veil.IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
syntax (name := deriveLawfulInstForFieldRepr) "deriving_lawful_FieldRepresentation" : command

def deriveLawfulInstForFieldRepresentation (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  /- Make sure `deriveFinEnumInstForToDomain` and `deriveRepInstForFieldReprentation` have been run before this command. -/
  let sortIdents ← mod.sortIdents false
  let finEnumInsts ← mod.instBinders ``FinEnum
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let mut binders := finEnumInsts ++ ordInsts ++ lawfulInsts ++ transInsts


  /- I do not know the reason compeletely now, but here we only need the `LawfulEqCmp` and `TransCmp` instances for the domain of `relation`.-/
  -- let stateDomains ← mod.getStateDomains
  -- for (_, doms) in stateDomains do
  --   let productDomain ← mkProdFromArray doms |> liftTermElabM
  --   let lawfulInst ← `(bracketedBinder| [$(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   let transInst ← `(bracketedBinder| [$(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
  --   binders := binders.push lawfulInst
  --   binders := binders.push transInst

  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain,
    mkIdent `instRepForFieldRepresentation,
    mkIdent ``Veil.IteratedProd',
    mkIdent `id
  ]
  let fIdent := mkIdent `f
  return ←
    `(command |
      instance $(mkIdent `instLawfulFieldRepForFieldRepresentation):ident $[$binders]*
      ($fIdent : $(mkIdent `State.Label):ident)
      : $(mkIdent ``Veil.LawfulFieldRepresentation) ( ($(mkIdent `State.Label.toDomain):ident $(← mod.sortIdents)*) $fIdent)
          ( ($(mkIdent `State.Label.toCodomain):ident $(← mod.sortIdents)*) $fIdent )
          ( ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)*) $fIdent )
          ( ($(mkIdent `instRepForFieldRepresentation):ident $(← mod.sortIdents)*) $fIdent ) :=
      by
        cases $fIdent:ident <;>
        first
        | (dsimp only [$[$dsimpTerms:ident],*]; infer_instance)
        | (exact $(mkIdent ``Veil.instFinsetLikeLawfulFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $(← mod.sortIdents)*) _))
    )

@[command_elab deriveLawfulInstForFieldRepr]
def deriveLawfulInstForFieldReprCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveLawfulInstForFieldRepresentation mod
  dbg_trace s!"deriving_lawful_fieldRepresentation : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd

-- instance rep
--   [FinEnum process]
--   [FinEnum states]
--   [Ord process]
--   [Ord states]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   (f : State.Label)
-- : FieldRepresentation ((⌞? State.Label.toDomain ⌟) f) ((⌞? State.Label.toCodomain ⌟) f) ((⌞? FieldConcreteType ⌟) f)
-- := by
--   cases f <;>
--   first
--   | (dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain]; infer_instance)
--   | (exact instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
--   | (exact instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
syntax (name := deriveRepInstForFieldRepr) "deriving_rep_FieldRepresentation" : command

def deriveRepInstForFieldReprentation (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  /- Make sure `deriveFinEnumInstForToDomain` has been run before this command. -/
  let typeBinders ← mod.typeExplicitBinders
  let sortIdents ← mod.sortIdents false
  let finEnumInsts ← mod.instBinders ``FinEnum
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let binders := typeBinders ++ finEnumInsts ++ ordInsts ++ lawfulInsts ++ transInsts

  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain,
  ]

  let fIdent := mkIdent `f
  return ←
    `(command |
      instance $(mkIdent `instRepForFieldRepresentation):ident $[$binders]*
      ($fIdent : $(mkIdent `State.Label):ident)
      : $(mkIdent ``FieldRepresentation) ( ($(mkIdent `State.Label.toDomain):ident $(← mod.sortIdents)*) $fIdent)
          ( ($(mkIdent `State.Label.toCodomain):ident $(← mod.sortIdents)*) $fIdent )
          ( ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)*) $fIdent ) :=
      by
        cases $fIdent:ident <;>
        first
        | (dsimp only [$[$dsimpTerms:ident],*]; infer_instance)
        | (exact $(mkIdent ``instFinsetLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $(← mod.sortIdents)*) _))
        | (exact $(mkIdent ``instTotalMapLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $(← mod.sortIdents)*) _))
    )


@[command_elab deriveRepInstForFieldRepr]
def deriveRepInstForFieldReprCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveRepInstForFieldReprentation mod
  dbg_trace s!"deriving_rep_fieldRepresentation : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd


-- instance
--   [Ord process]
--   [Ord states]
--   [FinEnum process]
--   [FinEnum states]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟))
--   := by
--   constructor ; constructor <;>
--   dsimp only [FieldConcreteType, State.Label.toCodomain, IteratedProd'] <;>
--   try exact default
syntax (name := derivingInhabitedInst) "deriving_Inhabited_State" : command

def deriveInhabitedInstForState (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents false
  let typeBinders ← mod.typeExplicitBinders
  let ordInsts ← mod.instBinders ``Ord
  let finEnumInst ← mod.instBinders ``FinEnum
  let inhabitedInsts ← mod.typeInhabitedBinders
  let decideableEqInsts ← mod.typeDecEqBinders
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)

 -- instance {cmp : α → α → Ordering} [FinEnum α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
--   ⟨⟨Std.TreeMap.ofList ((FinEnum.toList α).map (fun a => (a, default))) cmp,
--     by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp⟩⟩
  /- It's a little bit complex to derive the required minimal instances for this type. -/
  let binders := typeBinders ++ ordInsts ++ inhabitedInsts ++ decideableEqInsts ++ finEnumInst ++ lawfulInsts ++ transInsts

  let stateIdent := mkIdent `State
  let fieldConcreteTypeIdent := mkIdent `FieldConcreteType
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain,
    mkIdent ``Veil.IteratedProd'
  ]
  return ←
    `(command |
      instance $(mkIdent `instInhabitedFieldConcreteTypeForState):ident $[$binders]*
      : $(mkIdent ``Inhabited) ( ($stateIdent $(sortIdents)*) ( $fieldConcreteTypeIdent:ident $(sortIdents)* ) ) :=
      by
        constructor; constructor <;>
        dsimp only [$[$dsimpTerms:ident],*] <;>
        try exact $(mkIdent ``default)
    )

@[command_elab derivingInhabitedInst]
def deriveInhabitedInstCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveInhabitedInstForState mod
  dbg_trace s!"deriving_inhabited_state : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd



-- instance [Ord seq_t] [Ord Room] [Ord Guest] [Ord Position] [Ord Occupied]
-- [Repr seq_t] [Repr Room] [Repr Guest] [Repr Position] [Repr Occupied] :
--   (Repr (FieldConcreteType seq_t Room Guest Position Occupied State.Label.registered)) := by
--   dsimp only [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod
def deriveReprInstForFieldConcreteType (mod : Veil.Module) (stateLabelName : Name) : CommandElabM (TSyntax `command) := do
  let ordInst ← mod.instBinders ``Ord
  let reprInst ← mod.instBinders ``Repr
  let instBinders := ordInst ++ reprInst
  let instTargetTy ←
      `(term | ($(mkIdent ``Repr) ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)* $(mkIdent stateLabelName))))
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent ``Veil.IteratedProd',
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]
  return ← `(command |
    instance $(mkIdent $ (Name.appendBefore stateLabelName "instReprForFieldConcreteType_")):ident
      $[$instBinders]* : $instTargetTy := by
          dsimp only [$[$dsimpTerms:ident],*]
          repeat' (first | infer_instance | constructor)
  )
syntax (name := derivingReprFieldConcreteTypeCmd) "deriving_Repr_FieldConcreteType" : command
@[command_elab derivingReprFieldConcreteTypeCmd]
def deriveReprInstForFieldConcreteTypeCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames
  for lfIdent in labelFields do
    let lfName := Name.append `State.Label lfIdent
    let lfc ← deriveReprInstForFieldConcreteType mod lfName
    dbg_trace s!"deriving_Repr_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lfc}"
    elabVeilCommand lfc


-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod
syntax (name := derivingBEqFieldConcreteTypeCmd) "deriving_BEq_FieldConcreteType" : command

def deriveBEqInstForLabelField (mod : Veil.Module) (fieldName : Name)
  : CommandElabM (TSyntax `command) := do
  let stateLabelName := Name.append `State.Label fieldName

  let typeBinders ← mod.typeExplicitBinders
  /- BEq FieldConcreteType -/
  let decidableEqInsts ← mod.typeDecEqBinders
  let ordInst ← mod.instBinders ``Ord
  let allBinders := typeBinders ++ decidableEqInsts ++ ordInst

  let instTargetTy ←
      `(term | ($(mkIdent ``BEq) ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)* $(mkIdent stateLabelName))))
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent ``Veil.IteratedProd',
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]
  return ← `(command |
    instance $(mkIdent $ (fieldName.toInstName "instBEqForFieldConcreteType_")):ident
      $[$allBinders]* : $instTargetTy := by
          dsimp only [$[$dsimpTerms:ident],*]
          repeat' (first | infer_instance | constructor)
  )

@[command_elab derivingBEqFieldConcreteTypeCmd]
def deriveBEqInstForFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames

  for lfIdent in labelFields do
    let lfc ← deriveBEqInstForLabelField mod lfIdent
    dbg_trace s!"deriving_BEq_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lfc}"
    elabVeilCommand lfc




-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod
def deriveHashableInstForLabelField (mod : Veil.Module) (stateLabelName : Name) : CommandElabM (TSyntax `command) := do
  let typeBinders ← mod.typeExplicitBinders
  /- Deriving `Hashable` instance for each field (FieldConcreteType ... f) will
  finally reduce to giving an instance for `TreeSet α`, `TotalTreeMap α β`, e.g.,
  `⊢ Hashable (TreeSet (process × states) compare)`. Therefore, we should provide
  `Hashable` and `BEq` instances for used type parameters. We provide `DecideableEq`
  Here rather than `BEq`.

  This is an ad-hoc implementation, as sometimes we do not require that much instances.
   -/
  let decidableEqInsts ← mod.typeDecEqBinders
  let ordInst ← mod.instBinders ``Ord
  let hashInst ← mod.instBinders ``Hashable

  let instBinders := typeBinders ++ decidableEqInsts ++ ordInst ++ hashInst
  let instTargetTy ←
      `(term | ($(mkIdent ``Hashable) ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)* $(mkIdent stateLabelName))))
  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent `FieldConcreteType,
    mkIdent ``IteratedProd',
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]
  let ordCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent (stateLabelName.toInstName "instHashableForFieldConcreteType_")):ident
          $[$instBinders]* : $instTargetTy := by
              dsimp only [$[$dsimpTerms:ident],*]
              repeat' (first | infer_instance | constructor)
    )
  return ordCmd

syntax (name := derivingHashableFieldConcreteTypeCmd) "deriving_Hashable_FieldConcreteType" : command
@[command_elab derivingHashableFieldConcreteTypeCmd]
def deriveHashableInstForFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames
  for lfIdent in labelFields do
    let lfName := Name.append `State.Label lfIdent
    let lfc ← deriveHashableInstForLabelField mod lfName
    dbg_trace s!"deriving_Hashable_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lfc}"
    elabVeilCommand lfc


-- abbrev FieldConcreteType [Ord process] [Ord states] (f : State.Label)
--   : Type :=
--   match f with
--   | State.Label.locked =>
--     ((⌞? State.Label.toCodomain ⌟) State.Label.locked)
--   | State.Label.pc =>
--     Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pc)
--   /- `stack_pc` is a `function` field -/
--   | State.Label.stack_pc =>
--     Veil.TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_pc)
--     ((⌞? State.Label.toCodomain ⌟) State.Label.stack_pc)
/-
How to assembly `match...with` syntax
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Optional.20expected.20type.20in.20.60elab_rules.60/near/425853362
-/
def fieldsToMatchType (mod : Veil.Module) (fieldName : Name) (kind : StateComponentKind)
  : CommandElabM (TSyntax `Lean.Parser.Term.matchAltExpr) := do
  let caseIdent := mkIdent $ Name.append `State.Label fieldName
  let tSetIdent := mkIdent ``Std.TreeSet
  let ttMapIdent := mkIdent ``Veil.TotalTreeMap
  let sortIdents ← mod.sortIdents

  let mapKeyIdent : TSyntax `term ← `(term|
      ($(mkIdent ``Veil.IteratedProd') <| ($(mkIdent `State.Label.toDomain) $sortIdents*) $caseIdent:ident))
  let mapValueIdent : TSyntax `term ← `(term|
      (($(mkIdent `State.Label.toCodomain) $sortIdents*) $caseIdent:ident) )

  match kind with
  | .individual => `(Lean.Parser.Term.matchAltExpr|
    | $caseIdent:ident =>
      ($(mkIdent `State.Label.toCodomain) $sortIdents*) $caseIdent:ident)
  | .relation => `(Lean.Parser.Term.matchAltExpr|
    | $caseIdent:ident =>
      $tSetIdent:ident $mapKeyIdent:term)
  | .function =>  `(Lean.Parser.Term.matchAltExpr|
    | $caseIdent:ident =>
      $ttMapIdent:ident $mapKeyIdent $mapValueIdent:term)
  | .module =>
    throwError "Module kind is not supported in FieldConcreteType"


syntax (name := abbrevFieldConcreteType) "specify_FieldConcreteType" : command

@[command_elab abbrevFieldConcreteType]
def specifyFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let ordInst ← mod.instBinders ``Ord
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)))
  let typeBinders ← mod.typeExplicitBinders
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  -- let relName ← mod.relFieldNames
  let relName ← mod.fieldNames .relation
  let relCases ← relName.mapM fun rn => fieldsToMatchType mod rn .relation

  -- let funName ← mod.funFieldNames
  let funName ← mod.fieldNames .function
  let funCases ← funName.mapM fun fn => fieldsToMatchType mod fn .function

  -- let indivName ← mod.indivFieldNames
  let indivName ← mod.fieldNames .individual
  let indivCases ← indivName.mapM fun iname => fieldsToMatchType mod iname .individual

  let fieldConcreteTypeCmd : TSyntax `command ←
    `(command|
        abbrev $(mkIdent `FieldConcreteType):ident
          $[$allBinders]* : Type :=
            match $(mkIdent `f):ident with
              $indivCases:matchAlt*
              $relCases:matchAlt*
              $funCases:matchAlt*
    )
  dbg_trace s!"fieldConcreteTypeCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic fieldConcreteTypeCmd}"
  elabVeilCommand fieldConcreteTypeCmd


-- instance instToJsonForToDomain'
--   [ToJson process]
--   [ToJson states]
--   (f : State.Label)
-- : ToJson (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
-- cases f <;>
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance instToJsonForCodomain
--   [Lean.ToJson process]
--   [Lean.ToJson states]
--   (f : State.Label)
-- : Lean.ToJson ((⌞? State.Label.toCodomain ⌟) f) := by
-- cases f <;>
--   dsimp only [Veil.IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
--   infer_instance_for_iterated_prod

def deriveToJsonInstDomain (mod : Veil.Module) (toDomain : Bool := true): CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``ToJson
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let instToJsonName := if toDomain then `instToJsonForToDomain' else `instToJsonForToCodomain

  let stateLabelDomain ←
    if toDomain then
      `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)
    else
      `(term| $(mkIdent `State.Label.toCodomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    if toDomain then
      `(term | ($(mkIdent ``ToJson) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelDomain) $(mkIdent `f))))
    else
      `(term | ($(mkIdent ``ToJson) (($stateLabelDomain) $(mkIdent `f))))

  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]

  let toJsonCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent instToJsonName):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;> infer_instance
    )
  dbg_trace s!"toJsonCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic toJsonCmd}"
  elabVeilCommand toJsonCmd


-- instance instOrdForToDomain'
--   (f : State.Label)
--   [Ord process]
--   [Ord states]
--   : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;> dsimp only [IteratedProd', State.Label.toDomain] <;>
--   infer_instance

-- instance instOrdForToCodomain
--   [Ord process]
--   [Ord states]
--   (f : State.Label)
--   : Ord (⌞? State.Label.toCodomain ⌟ f) := by
--   cases f <;> dsimp only [State.Label.toCodomain] <;> infer_instance

/- Derive `Ord` instance for both `toDomain` and `toCodomain` -/
def deriveOrdInstForDomain (mod : Veil.Module) (toDomain : Bool := true) : CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``Ord
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let instName := if toDomain then `instOrdForToDomain' else `instOrdForToCodomain

  let stateLabelDomain ←
    if toDomain then
      `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)
    else
      `(term| $(mkIdent `State.Label.toCodomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    if toDomain then
      `(term| ($(mkIdent ``Ord) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelDomain) $(mkIdent `f))))
    else
      `(term| ($(mkIdent ``Ord) (($stateLabelDomain) $(mkIdent `f))))

  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]

  let ordCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent instName):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;>
              infer_instance
    )
  dbg_trace s!"ordCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic ordCmd}"
  elabVeilCommand ordCmd


-- def instFinEnumForToDomain
--   [FinEnum process]
--   [FinEnum states]
--   (f : State.Label)
--   : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--    infer_instance_for_iterated_prod
def deriveFinEnumInstForToDomain (mod : Veil.Module) : CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let finEnumInst ← mod.instBinders ``FinEnum
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ finEnumInst ++ [labelBinder]

  let stateLabelToDomain ←
    `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    `(term | ($(mkIdent ``IteratedProd) <| ($(mkIdent ``List.map) $(mkIdent ``FinEnum) <| ($stateLabelToDomain) $(mkIdent `f))))
  let finEnumCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent `instFinEnumForToDomain):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              infer_instance_for_iterated_prod
    )
  dbg_trace s!"finEnumCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic finEnumCmd}"
  elabVeilCommand finEnumCmd


-- instance instFinEnumForToDomain'
--   [FinEnum process]
--   [FinEnum states]
--   (f : State.Label)
--   : FinEnum (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', List.foldr, State.Label.toDomain] <;>
--     infer_instance
def deriveFinEnumInstForToDomain' (mod : Veil.Module): CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let finEnumInst ← mod.instBinders ``FinEnum
  let labelBinder ←
    `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ finEnumInst ++ [labelBinder]

  let stateLabelToDomain ←
    `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)

  let instTargetTy ← `(term | $(mkIdent ``FinEnum) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelToDomain) $(mkIdent `f)))
  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain
  ]
  let finEnumCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent `instFinEnumForToDomain'):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;>
              infer_instance
    )
  elabVeilCommand finEnumCmd



syntax (name := derivingToJsonState) "deriving_FinOrdToJson_Domain" : command

@[command_elab derivingToJsonState]
def GetFieldsNameFieldsName : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let sig := mod.signature
  let kind' := sig.map (fun f => f.kind)
  let fieldNames := sig.map (fun f => f.name)
  let mutability := sig.map (fun f => f.mutability)
  let stateComponentType := sig.map (fun f => f.type)

  -- inductive StateComponentType where
  --   /-- e.g. `stateComponentName : Int -> vertex -> Prop` -/
  --   | simple (t : TSyntax ``Command.structSimpleBinder)
  --   /-- e.g. `(r : Int) (v : vertex)` and `Prop` -/
  --   | complex (binders : TSyntaxArray ``Term.bracketedBinder) (dom : Term)
  -- deriving Inhabited, BEq
  for s in sig do
    let sc := s.type
    dbg_trace s!"Field: {s.name}, Kind: {s.kind}, Mutability: {s.mutability}"
    match sc with
    | .simple t =>
      dbg_trace s!"simple Type: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic t}"
    | .complex binders dom =>
      let stx ← `(def $(mkIdent `NameT):ident $[$binders]* := $dom:term)
      dbg_trace s!"Complex Type: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}\n"
      -- let fmt ← PrettyPrinter.ppCategory Parser.Category.term stx

    for (name, res) in (← mod.getStateDomains) do
      dbg_trace s!"State Domain Field: {name}, Domains: {res}"

  -- dbg_trace s!"Field Names: {fieldNames}"
  -- dbg_trace s!"Field Mutability: {mutability}"

  -- let relFieldNames ← mod.relFieldNames
  -- let indivFieldNames ← mod.indivFieldNames
  -- let funFieldNames ← mod.funFieldNames
  -- dbg_trace s!"Relation Field Names: {relFieldNames}"
  -- dbg_trace s!"Individual Field Names: {indivFieldNames}"
  -- dbg_trace s!"Function Field Names: {funFieldNames}"

  -- let enumTypes ← mod.typeIdents true
  -- let nonEnumTypes ← mod.typeIdents false
  -- dbg_trace s!"Enum Types: {enumTypes}"
  -- dbg_trace s!"Non-enum Types: {nonEnumTypes}"

  deriveFinEnumInstForToDomain mod
  deriveFinEnumInstForToDomain' mod
  deriveOrdInstForDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := false)



syntax (name := derivingDecInsts) "deriving_Decidable_Props" : command


/- `mod.mkVeilTerm` was `private def` before, which is in `Veil.Frontend.DSL.Module.Util`. Here I made it accessible, removing `private`. -/
/- Derive `Decidable` instanecs for invariants should be  -/
-- open Lean.Parser in
@[command_elab derivingDecInsts]
def deriveDecidableForProps : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_Decidable_Props) => do
    let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    let props := mod.invariants ++ mod.terminations
    for base in props do
      -- let justTheory := match base.kind with | .assumption => true | _ => false
      -- let (extraParams, thstBinders, term) ← liftTermElabM $ mod.mkVeilTerm base.name base.declarationKind (params := .none) base.term (justTheory := justTheory)
      -- This includes the required `Decidable` instances
      -- let (binders, _) ← mod.declarationAllParamsMapFn (·.binder) base.name base.declarationKind
      -- dbg_trace s!"Invariant binders: {binders}"
      -- let binders := (← binders.mapM mkImplicitBinder)
      -- let binders := binders.filter (fun x => !(isTypeBinder x))
      let sortIdents ← mod.sortIdents
      let explicitBinder := #[
            ← `(bracketedBinder| ($(mkIdent `rd) : $(mkIdent `ρ))),
            ← `(bracketedBinder| ($(mkIdent `st) : $(mkIdent `σ))) ]
      let finEnumInst ← sortIdents.mapM (fun t => do
          `(bracketedBinder| [$(mkIdent ``FinEnum) $t])
      )
      -- let newBs := binders ++ extra
      let binder := explicitBinder ++ finEnumInst
      let stx ← `(
        instance $[$binder]* : $(mkIdent ``Decidable) ($(mkIdent base.name) $(mkIdent `rd) $(mkIdent `st)) := by
          dsimp [$(mkIdent base.name):ident];
          infer_instance
      )
      elabVeilCommand stx
      dbg_trace s!"Elaborated invariant definition: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  | _ => throwUnsupportedSyntax



syntax (name := derivingDeciableInsts) "deriving_DecidableProps_state" : command
-- instance (rd : TheoryConcrete) (st : StateConcrete) : Decidable ((fun ρ σ => no_future_keys ρ σ) rd st) :=
--   by
--   dsimp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain, no_future_keys]
--   infer_instance
@[command_elab derivingDeciableInsts]
def deriveDecidablePropsForConcreteState : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_DecidableProps_state) => do
    let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    let props := mod.invariants ++ mod.terminations
    for base in props do
      -- let sortIdents ← mod.sortIdents
      let explicitBinder := #[
            ← `(bracketedBinder| ($(mkIdent `rd) : $(mkIdent `TheoryConcrete) )),
            ← `(bracketedBinder| ($(mkIdent `st) : $(mkIdent `StateConcrete) )) ]
      let binder := explicitBinder
      let stx ← `(
        instance $[$binder]* : $(mkIdent ``Decidable) ($(mkIdent base.name) $(mkIdent `rd) $(mkIdent `st)) := by
          dsimp [$(mkIdent base.name):ident, $(mkIdent `FieldConcreteType):ident, $(mkIdent `State.Label.toDomain):ident, $(mkIdent `State.Label.toCodomain):ident];
          infer_instance
      )
      elabVeilCommand stx
      dbg_trace s!"Elaborated invariant definition for Concrete State: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  | _ => throwUnsupportedSyntax




syntax (name := concretizeTypeCmd) "#Concretize" term,* : command
/-- Generate label list (labelList) definition -/
def getLabelList : CommandElabM Unit := do
  trace[veil.info] "[getLabelList] Starting label list generation"
  -- Check if labelList already exists
  let labelListDefName := (← getCurrNamespace) ++ `labelList
  if (← getEnv).contains labelListDefName then
    trace[veil.info] "[getLabelList] labelList already exists, skipping"
    return

  let labelConcreteName ← resolveGlobalConstNoOverloadCore `LabelConcrete
  -- Generate labelList definition using the pattern from BakeryMC.lean
  let labelListCmd ← liftTermElabM do
    let labelListIdent := mkIdent `labelList
    let labelConcreteIdent := mkIdent labelConcreteName
    `(command|
      def $labelListIdent := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv%($labelConcreteIdent)))).toList)
  trace[veil.debug] "[getLabelList] {labelListCmd}"
  elabVeilCommand labelListCmd


elab "#Concretize" args:term,* : command => do
    -- let env ← getEnv
    let termArray := args.getElems

    let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    /- The `State`, `Theory` and `Label` can only be used after `#gen_spec` run -/
    if !Module.isSpecFinalized mod then
      throwError "The module specification should be finalized before concretizing types."
    let FieldConcreteTypeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `FieldConcreteType)

    let theoryConcreteName := `TheoryConcrete
    let stateConcreteName := `StateConcrete
    let labelConcreteName := `LabelConcrete

    -- build `TheoryConcrete`
    let theoryCmd ← do
      let assembledTheory ←`(term| @$(mkIdent theoryName) $termArray*)
      -- dbg_trace s!"TheoryConcrete assembledTheory: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic assembledTheory}"
      `(command| @[reducible] def $(mkIdent theoryConcreteName) := $assembledTheory)

    -- build `LabelConcrete`
    let labelCmd ← do
      let assembledLabel ←`(term| @$(mkIdent labelTypeName) $termArray*)
      -- dbg_trace s!"LabelConcrete assembledLabel: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic assembledLabel}"
      `(command| @[reducible] def $(mkIdent labelConcreteName) := $assembledLabel)

    -- build `FieldConcreteTypeInst`
    let fieldConcreteInstCmd ← do
      let assembledFieldConcreteInst ←`(term | $(mkIdent FieldConcreteTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent `FieldConcreteTypeInst) := $assembledFieldConcreteInst)

    -- build `StateConcrete`
    let stateCmd ← do
      let assembledState ← `(term| @$(mkIdent stateName) $termArray*)
      let fieldConcreteInstTerm ← `(term | $(mkIdent `FieldConcreteType) $termArray*)
      -- dbg_trace s!"StateConcrete assembledState: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic assembledState}"
      `(command| @[reducible] def $(mkIdent stateConcreteName) := ($assembledState) $fieldConcreteInstTerm)

    elabVeilCommand theoryCmd
    elabVeilCommand labelCmd
    elabVeilCommand fieldConcreteInstCmd
    elabVeilCommand stateCmd

    -- build `initVeilMultiExecM`
    let initCmd ← do
      let assembledInitM ←`(term|
        ((( $(mkIdent `initMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
        $termArray* )
        $(mkIdent `FieldConcreteTypeInst) ) )
      `(command| def $(mkIdent `initVeilMultiExecM) := $assembledInitM)

    -- build `nextVeilMultiExecM`
    let nextCmd ← do
      let assembledNextM ←`(term|
        ( (( $(mkIdent `nextActMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
            $termArray* )
          /-$(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `nextVeilMultiExecM) := $assembledNextM)

    elabVeilCommand initCmd
    elabVeilCommand nextCmd
    getLabelList



def deriveBEqForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames ← mod.stateFieldNames
  -- build `BEq` instance for `StateConcrete`
  let s1 := mkIdent `s1
  let s2 := mkIdent `s2
  let eqTerms : Array (TSyntax `term) ← fieldNames.mapM (fun f => do
    `(term| $s1.$(mkIdent f) == $s2.$(mkIdent f)))

  let beqBody : TSyntax `term ← do
    if h : eqTerms.size = 0 then
      `(term| True)
    else
      let mut acc := eqTerms[0]
      for i in [1:eqTerms.size] do
        acc ← `(term| $acc && $(eqTerms[i]!))
      pure acc

  let BEqInstCmd : Syntax ←
    `(command|
        instance : $(mkIdent ``BEq) $(mkIdent `StateConcrete) where
          $(mkIdent `beq):ident := fun $s1 $s2 => $beqBody)
  dbg_trace s!"BEqInstCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic BEqInstCmd}"
  elabVeilCommand BEqInstCmd


def deriveHashableForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames ← mod.stateFieldNames
  -- build `Hashable` instance for `StateConcrete`
  let s := mkIdent `s
  let binds : Array (Name × TSyntax `term) ←
    fieldNames.mapM (fun f => do
      let rhs ← `(term| $(mkIdent ``hash) $s.$(mkIdent f))
      pure (f, rhs))

  -- 3) build final body: hash (rhs₁, rhs₂, ..., rhsₙ)
  let hashIds : Array (TSyntax `term) :=
    fieldNames.map (fun f => (mkIdent f : TSyntax `term))
  let finalBody : TSyntax `term ← liftMacroM <| mkTuple hashIds

  -- 4) from right to left: let xₙ := rhsₙ; ...; let x₁ := rhs₁; finalBody
  let body : TSyntax `term ←
    binds.foldrM (init := finalBody) (fun (f, rhs) acc =>
      `(term| let $(mkIdent f) := $rhs; $acc))

  -- 5) assemble instance (use lambda to bind parameters to avoid binder category mismatch)
  let HashableInstCmd : TSyntax `command ←
    `(command|
        instance : $(mkIdent ``Hashable) $(mkIdent `StateConcrete) where
          $(mkIdent `hash):ident := fun $s => $(mkIdent ``hash) $body)
  dbg_trace s!"tryVlsUnfold : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic HashableInstCmd}"
  elabVeilCommand HashableInstCmd
where
  mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
    match xs.size with
    | 0 => `(term| ())
    | 1 => pure xs[0]!
    | _ =>
      let mut acc : TSyntax `term ← `(term| ($(xs[0]!), $(xs[1]!)))
      for i in [2:xs.size] do
        acc ← `(term| ($acc, $(xs[i]!)))
      return acc

instance [FinEnum α] : BEq α := by infer_instance



elab "deriving_BEqHashable_ConcreteState" : command => do
  let mod ← getCurrentModule
  deriveBEqForState mod
  deriveHashableForState mod

-- instance jsonOfState : ToJson StateConcrete where
--   toJson := fun s =>
--     Json.mkObj
--     [ ("locked",            Lean.toJson s.locked)
--     , ("wait_queue_wakers", Lean.toJson s.wait_queue_wakers)
--     , ("has_woken",         Lean.toJson s.has_woken)
--     , ("pc",                Lean.toJson s.pc)
--     , ("stack_pc",          Lean.toJson s.stack_pc)
--     , ("stack_waker",       Lean.toJson s.stack_waker)
--     , ("waker",             Lean.toJson s.waker)
--     ]

def deriveToJsonForState (mod : Veil.Module) : CommandElabM Unit := do
  let sId := mkIdent `s

  let fieldNames ← mod.stateFieldNames
  let pairs : Array (TSyntax `term) ← fieldNames.mapM (fun fName => do
    let fieldStr := fName.toString
    let lit      := Syntax.mkStrLit fieldStr
    let projId   := mkIdent fName
    `(term| ($lit, $(mkIdent ``toJson) $sId.$projId))
  )

  let toJsonRhs ← `(term| fun $sId => $(mkIdent ``Json.mkObj) [ $[$pairs],* ])
  let instToJsonIdent := (mkIdent `jsonOfState)
  let traceToJsonInst ←
    `(command|
      instance $instToJsonIdent:ident : $(mkIdent ``ToJson) $(mkIdent `StateConcrete) where
        $(mkIdent `toJson):ident := $toJsonRhs)
  dbg_trace s!"toJsonCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic traceToJsonInst}"
  elabVeilCommand traceToJsonInst

syntax (name := derivingToJsonForState) "deriving_toJson_for_state" : command

@[command_elab derivingToJsonForState]
def deriveToJsonForStateElab : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  deriveToJsonForState mod




syntax (name := veilMakeExecutable) "#prepareExecution" : command

macro_rules
  | `(command| #prepareExecution) => do
    `(-- Step 1: Make symbolic model executable by deriving required instances
      simple_deriving_repr_for' $(mkIdent `State)
      deriving instance $(mkIdent ``Repr) for $(mkIdent `Label)
      deriving instance $(mkIdent ``Inhabited) for $(mkIdent `Theory)
      deriving_FinOrdToJson_Domain
      specify_FieldConcreteType
      deriving_BEq_FieldConcreteType
      deriving_Hashable_FieldConcreteType
      deriving_rep_FieldRepresentation
      deriving_lawful_FieldRepresentation
      deriving_Inhabited_State
      gen_NextAct
      gen_executable_NextAct)


syntax (name := veilFinitizeTypes) "#finitizeTypes" term,* : command

macro_rules
  | `(command| #finitizeTypes $args:term,*) => do
    `(-- Step 2: Finitize abstract types to enable model checking
      deriving_Enum_Insts
      #Concretize $args,*
      deriving_BEqHashable_ConcreteState
      deriving_toJson_for_state
      deriving_DecidableProps_state)
