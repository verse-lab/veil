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
  let baseClasses := #[``DecidableEq, ``Repr].map Lean.mkIdent
  let derivings := if !ctors.isEmpty then baseClasses ++ (#[ ``Inhabited, ``Nonempty].map Lean.mkIdent) else baseClasses
  let indType ← `(inductive $name where $[$ctors]* deriving $[$derivings:ident],*)
  -- show that the concrete type satisfies the axiomatisation
  let concElems : Array Ident := elems.map fun el => mkIdent (name.getId ++ el.getId)
  let instFields ← (elems.zip concElems).mapM fun (el, concEl) => `(Lean.Parser.Term.structInstField| $el:ident := $concEl:ident)
  let distinctField ← `(Lean.Parser.Term.structInstField| $enumDistinct:ident :=  (by (try decide); (try grind)))
  let completeField ← do
    let x := mkVeilImplementationDetailIdent `x
    `(Lean.Parser.Term.structInstField| $enumComplete:ident := (by intro $x:ident <;> cases $x:ident <;> (first | decide | grind)))
  let fields := instFields ++ #[distinctField, completeField]
  let instanceAx ← `(command|scoped instance : $(Ident.toEnumClass id) $name where $[$fields]*)
  -- derive instances for the concrete type
  let derivedInsts ← do
    let insts := #[``Ord, ``Hashable, ``Enumeration, ``FinEncodable, ``Std.TransOrd, ``Std.LawfulEqOrd].map Lean.mkIdent
    `(command| deriving instance $[$insts:ident],* for $name)
  return #[indType, instanceAx, derivedInsts]

end Veil
