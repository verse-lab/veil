import Veil.Frontend.DSL.Module.Util.Basic

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## Enum-like Type Generation Helpers -/

/-- Generate a disjunction of equality constraints: `x = a ∨ x = b ∨ ...` -/
private def isEqualToOneOf {m} [Monad m] [MonadQuotation m] (x : TSyntax `term) (xs : Array (TSyntax `term)) : m (TSyntax `term) := do
  let equalities ← xs.mapM (fun elem => `($x = $(elem)))
  repeatedOr equalities

/-- Generate an axiomatisation class for an enum-like type with `distinctN` and `complete` axioms.
    Used for both user-defined enums and generated ActionTag types. -/
def mkEnumAxiomatisation {m} [Monad m] [MonadQuotation m] (id : Ident) (elems : Array Ident) : m (Ident × TSyntax `command) := do
  let variants ← elems.mapM (fun elem => `(Command.structSimpleBinder|$elem:ident : $id))
  let (class_name, ax_distinct, ax_complete) := (Ident.toEnumClass id, enumDistinct, enumComplete)
  let ax_distinct ←
    `(Command.structSimpleBinder|$ax_distinct:ident : $(mkIdent ``distinctN) [$[$elems],*])
  let x := mkVeilImplementationDetailIdent `x
  let ax_complete ← `(Command.structSimpleBinder|$ax_complete:ident : ∀ ($x : $id), $(← isEqualToOneOf x elems))
  let class_decl ← `(
    class $class_name ($id : $(mkIdent ``outParam) Type) where
      $[$variants]*
      $ax_distinct
      $ax_complete)
  return (class_name, class_decl)

/-- Generate a concrete inductive type and instances for an enum-like type.
    Used for both user-defined enums and generated ActionTag types. -/
def mkEnumConcreteType {m} [Monad m] [MonadQuotation m] (id : Ident) (elems : Array Ident) : m (Array (TSyntax `command)) := do
  let name := Ident.toEnumConcreteType id
  let ctors ← elems.mapM fun el => `(Lean.Parser.Command.ctor| | $el:ident )
  let baseClasses := #[``DecidableEq].map Lean.mkIdent
  let derivings := if !ctors.isEmpty then baseClasses ++ (#[ ``Inhabited, ``Nonempty].map Lean.mkIdent) else baseClasses
  let indType ← `(inductive $name where $[$ctors]* deriving $[$derivings:ident],*)
  let reprInst ← do
    let x := mkVeilImplementationDetailIdent `x
    let fallback ← `(term| "<unrepresentable>")
    let reprBody ← elems.foldrM (init := fallback) fun (el : Ident) (acc : Term) => do
      let concEl := Lean.mkIdent (name.getId ++ el.getId)
      `(term| if $x:ident = $concEl:ident then $(Syntax.mkStrLit el.getId.getString!) else $acc)
    `(command|
      instance : $(Lean.mkIdent ``Repr) $name where
        $(Lean.mkIdent `reprPrec):ident $x:ident _ := $reprBody)
  let toJsonInst ← `(command|
    instance : $(Lean.mkIdent ``Lean.ToJson) $name where
      $(Lean.mkIdent `toJson):ident x := $(Lean.mkIdent ``Lean.Json.str) ($(Lean.mkIdent ``reprStr) x))
  -- show that the concrete type satisfies the axiomatisation
  let concElems : Array Ident := elems.map fun el => Lean.mkIdent (name.getId ++ el.getId)
  let instFields ← (elems.zip concElems).mapM fun (el, concEl) => `(Lean.Parser.Term.structInstField| $el:ident := $concEl:ident)
  let distinctField ← `(Lean.Parser.Term.structInstField| $enumDistinct:ident :=  (by (try decide); (try grind)))
  let completeField ← do
    let x := mkVeilImplementationDetailIdent `x
    `(Lean.Parser.Term.structInstField| $enumComplete:ident := (by intro $x:ident <;> cases $x:ident <;> (first | decide | grind)))
  let fields := instFields ++ #[distinctField, completeField]
  let instanceAx ← `(command|scoped instance : $(Ident.toEnumClass id) $name where $[$fields]*)
  -- derive instances for the concrete type
  let derivedInsts ← do
    let insts := #[``Hashable, ``Enumeration, ``FinEncodable].map Lean.mkIdent
    `(command| deriving instance $[$insts:ident],* for $name)
  let ordInst ← `(command| instance : $(mkIdent ``Ord) $name := $(mkIdent ``Veil.Ord.ofFinEncodable) $name)
  let transOrdInst ← `(command| instance : $(mkIdent ``Std.TransOrd) $name := $(mkIdent ``Veil.Std.TransOrd.ofFinEncodable) $name)
  let lawfulEqOrdInst ← `(command| instance : $(mkIdent ``Std.LawfulEqOrd) $name := $(mkIdent ``Veil.Std.LawfulEqOrd.ofFinEncodable) $name)
  return #[indType, reprInst, toJsonInst, instanceAx, derivedInsts, ordInst, transOrdInst, lawfulEqOrdInst]

end Veil
