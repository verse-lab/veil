import Veil.Frontend.DSL.Module.Util.Basic

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## Enum-like Type Generation Helpers -/

/-- Generate a disjunction of equality constraints: `x = a ∨ x = b ∨ ...` -/
private def isEqualToOneOf {m} [Monad m] [MonadQuotation m] (x : TSyntax `term) (xs : Array (TSyntax `term)) : m (TSyntax `term) := do
  let equalities ← xs.mapM (fun elem => `($x = $(elem)))
  repeatedOr equalities

/-- Generate an axiomatisation class for an enum-like type with `distinct` and `complete` axioms.
    Used for both user-defined enums and generated ActionTag types. -/
def mkEnumAxiomatisation {m} [Monad m] [MonadQuotation m] (id : Ident) (elems : Array Ident) : m (Ident × TSyntax `command) := do
  let variants ← elems.mapM (fun elem => `(Command.structSimpleBinder|$elem:ident : $id))
  let (class_name, ax_distinct, ax_complete) := (Ident.toEnumClass id, enumDistinct, enumComplete)
  let ax_distinct ← `(Command.structSimpleBinder|$ax_distinct:ident : distinct $[$elems]*)
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
  let indType ← do
    if !ctors.isEmpty then
      `(inductive $name where $[$ctors]* deriving $(mkIdent ``DecidableEq):ident, $(mkIdent ``Repr):ident, $(mkIdent ``Inhabited):ident, $(mkIdent ``Nonempty):ident)
    else
      `(inductive $name where deriving $(mkIdent ``DecidableEq):ident, $(mkIdent ``Repr):ident)
  -- show that the concrete type satisfies the axiomatisation
  let concElems : Array Ident := elems.map fun el => mkIdent (name.getId ++ el.getId)
  let instFields ← (elems.zip concElems).mapM fun (el, concEl) => `(Lean.Parser.Term.structInstField| $el:ident := $concEl:ident)
  let distinctField ← `(Lean.Parser.Term.structInstField| $enumDistinct:ident :=  (by (try decide); (try grind)))
  let completeField ← do
    let x := mkVeilImplementationDetailIdent `x
    `(Lean.Parser.Term.structInstField| $enumComplete:ident := (by intro $x:ident <;> cases $x:ident <;> (first | decide | grind)))
  let fields := instFields ++ #[distinctField, completeField]
  let instanceAx ← `(command|instance : $(Ident.toEnumClass id) $name where $[$fields]*)
  -- show that the concrete type is a `Veil.Enumeration`
  let constructors ← `(term| [ $concElems,* ] )
  let complete : Ident := mkIdent $ Name.toEnumClass id.getId ++ enumCompleteName
  let instanceEnumeration ←
    `(instance : $(mkIdent ``Enumeration) $name := $(mkIdent ``Enumeration.mk) $constructors (by simp ; exact $complete))
  -- derive instances for the concrete type
  let derivedInsts ← `(command| deriving instance $(mkIdent ``Ord):ident, $(mkIdent ``Hashable):ident for $name)
  -- we derive instances for `Std.OrientedCmp`, `Std.TransCmp`, and `Std.LawfulEqCmp` manually
  let ord ← `($(mkIdent ``Ord.compare) ($(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $name)))
  let instMk := fun ty => `(command| instance : $(mkIdent ty) $ord := by apply$(mkIdent $ ty ++ `mk) ; decide)
  let ordInsts ← #[``Std.OrientedCmp, ``Std.TransCmp, ``Std.LawfulEqCmp].mapM instMk
  return #[indType, instanceAx, instanceEnumeration, derivedInsts] ++ ordInsts

end Veil
