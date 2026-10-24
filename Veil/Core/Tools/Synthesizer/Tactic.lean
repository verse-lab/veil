module

public meta import Veil

/-!
# Tactics for concrete certificates

The counterexample certificate proves facts about concrete states: that the theory satisfies the
assumptions, that a state is initial, that a step is a transition, that a state violates the
property. After Veil's definitions are unfolded, each fact is a proposition about finite values.

## Main definitions

* `veil_enum_cases`: split the variables of enumeration types into their constructors.
* `veil_concrete [defs]`: prove a proposition about concrete values.

## Implementation notes

A Veil action compares values of an enum sort through the enum's class, which neither `decide`
nor `simp` evaluates while the compared value is a variable. Splitting such variables into
constructors lets `simp` evaluate each comparison.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Meta Tactic

/-- Whether `ty` is an enumeration type with at least two constructors. -/
def isSplittableEnum (ty : Expr) : MetaM Bool := do
  let .const n _ := (← whnf ty).getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? n | return false
  return info.ctors.length > 1 && (← isEnumType n)

/-- Split every hypothesis of an enumeration type into its constructors, recursively, at most
`depth` levels deep. -/
def splitEnumHyps (g : MVarId) : (depth : Nat) → MetaM (List MVarId)
  | 0 => pure [g]
  | depth + 1 => g.withContext do
    let some d ← (← getLCtx).findDeclM? fun d ↦ do
        return if !d.isImplementationDetail && (← isSplittableEnum d.type) then some d else none
      | return [g]
    let subgoals ← g.cases d.fvarId
    return (← subgoals.toList.mapM (splitEnumHyps ·.mvarId depth)).flatten

/-- `veil_enum_cases` splits every hypothesis whose type is an enumeration type (an inductive type
whose constructors take no arguments, such as the concrete type of an enum sort) into its
constructors. -/
elab "veil_enum_cases" : tactic => liftMetaTactic (splitEnumHyps · 64)

/-- `veil_concrete [defs]` proves a proposition about concrete values: by evaluation, or else by
simplification with the definitions `defs` of the values, splitting the variables of enumeration
types into their constructors (`veil_enum_cases`) when that does not suffice. -/
syntax "veil_concrete " "[" ident,* "]" : tactic

macro_rules
  | `(tactic| veil_concrete [$defs,*]) => do
    let defs := defs.getElems
    `(tactic| first
      | decide
      | (simp +instances [$[$defs:ident],*]
         all_goals (intros; veil_enum_cases)
         all_goals simp_all +instances [$[$defs:ident],*]))

end Veil.Synthesizer
