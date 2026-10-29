module

public import Veil

set_option veil.smt.trust false

public class UnrelatedRootClass where
  flag : Bool

public class SourceChoice where
  chosen : Nat

@[reducible, expose, instance] public def originalChoice : SourceChoice := ⟨nat_lit 1⟩

public instance : Inhabited (OfNat Nat (nat_lit 1)) := ⟨⟨nat_lit 1⟩⟩

veil module FixedInstanceSource

individual value : Nat
individual bounded : Fin 1

after_init {
  value := 0
  bounded := 0
}

procedure assign_one {
  value := 1
  ensure value = 1
}

procedure get_one { return 1 }
procedure get_choice { return SourceChoice.chosen }

action set_one {
  assign_one
  ensure value = 1
}

invariant [value_bound] value ≤ 1

#gen_spec
end FixedInstanceSource

veil module ValueDictionarySource

param dictionary : OfNat Nat (nat_lit 1)
individual value : Nat
after_init {
  value := 1
}
action restore { value := 1 }
invariant [value_is_one] value = 1

#gen_spec
end ValueDictionarySource

-- This was not in the source declaration's instance environment.
@[reducible, expose, instance 2000] public def laterChoice : SourceChoice := ⟨nat_lit 9⟩

public structure LaterNumber where
  value : Nat

@[default_instance 2000, reducible, expose]
public def laterNumberOne : OfNat LaterNumber (nat_lit 1) := ⟨⟨nat_lit 1⟩⟩

veil module FixedInstanceRoot

instantiate customOne : OfNat Nat (nat_lit 1)
instantiate unrelated : UnrelatedRootClass
individual callerValue : Nat
isolate s : FixedInstanceSource

action caller_uses_custom { callerValue := 1 }

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

-- The source field's type is fixed before aggregate State generation.
example : State.Label.inst_1_s__field__bounded.toCodomain = Fin (nat_lit 1) := rfl

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in [`FixedInstanceRoot.inst_1_s__procedure__assign_one.do,
      `FixedInstanceRoot.inst_1_s__invariant__value_bound,
      `FixedInstanceRoot.inst_1_s__initializer.do] do
    let info ← getConstInfo name
    let some value := info.value? | throwError "missing source body {name}"
    if value.getUsedConstants.contains ``laterChoice then
      throwError "a later global instance changed source elaboration: {name}"
    lambdaTelescope value fun arguments body => do
      for argument in arguments do
        let decl ← argument.fvarId!.getDecl
        if decl.userName == `customOne || decl.userName == `unrelated then
          if (collectFVars {} body).fvarIds.contains argument.fvarId! then
            throwError "a caller-only local instance changed source elaboration: {name}"
  let choice ← getConstInfo `FixedInstanceRoot.inst_1_s__procedure__get_choice.do
  let some choiceBody := choice.value? | throwError "missing source choice body"
  unless choiceBody.getUsedConstants.contains ``originalChoice do
    throwError "the source global dictionary was not preserved"
  if choiceBody.getUsedConstants.contains ``laterChoice then
    throwError "a later global dictionary changed the source body"
  let info ← getConstInfo `FixedInstanceRoot.caller_uses_custom.do
  let some value := info.value? | throwError "missing caller body"
  let used ← lambdaTelescope value fun arguments body => do
    arguments.anyM fun argument => do
      let decl ← argument.fvarId!.getDecl
      return decl.userName == `customOne &&
        (collectFVars {} body).fvarIds.contains argument.fvarId!
  unless used do
    throwError "source instance restriction leaked into caller code"
  let info ← getConstInfo `FixedInstanceRoot.inst_1_s__procedure__get_one.do
  forallTelescope info.type fun _ returnType => do
    unless ← isDefEq returnType.getAppArgs.back! (mkConst ``Nat) do
      throwError "a later default instance changed the source procedure's result type"

end FixedInstanceRoot

veil module DeclaredInstanceSource

instantiate one : OfNat Nat (nat_lit 1)
individual value : Nat
after_init { value := 1 }
procedure assign_one { value := 1 }
action restore { assign_one }
invariant [value_is_one] value = 1

#gen_spec
end DeclaredInstanceSource

veil module DistinctSourceInstances

instantiate callerOne : OfNat Nat (nat_lit 1)
instantiate unrelated : UnrelatedRootClass
isolate a : DeclaredInstanceSource
isolate b : DeclaredInstanceSource

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

-- Identical class types do not identify the two occurrence bindings.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for (name, expected) in [
      (`DistinctSourceInstances.inst_1_a__procedure__assign_one.do, `inst_1_a__instance__one),
      (`DistinctSourceInstances.inst_1_b__procedure__assign_one.do, `inst_1_b__instance__one)] do
    let info ← getConstInfo name
    let some value := info.value? | throwError "missing source body {name}"
    let found ← lambdaTelescope value fun arguments body => do
      let mut found := false
      for argument in arguments do
        let decl ← argument.fvarId!.getDecl
        if #[`callerOne, `inst_1_a__instance__one, `inst_1_b__instance__one].contains decl.userName then
          let used := (collectFVars {} body).fvarIds.contains argument.fvarId!
          unless used == (decl.userName == expected) do
            throwError "wrong occurrence instance selected in {name}: {decl.userName}"
          found := found || (used && decl.userName == expected)
      return found
    unless found do throwError "source class requirement was lost in {name}"

end DistinctSourceInstances

veil module ValueDictionaryRoot

param callerDictionary : OfNat Nat (nat_lit 1)
instantiate unrelated : UnrelatedRootClass
isolate fixed : FixedInstanceSource
isolate chosen : ValueDictionarySource
  (dictionary := (⟨nat_lit 5⟩ : OfNat Nat (nat_lit 1)))

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let info ← getConstInfo `ValueDictionaryRoot.inst_5_fixed__procedure__assign_one.do
  let some value := info.value? | throwError "missing fixed source body"
  lambdaTelescope value fun arguments body => do
    for argument in arguments do
      if (← argument.fvarId!.getDecl).userName == `callerDictionary then
        if (body.find? fun expression =>
            expression.isAppOfArity ``OfNat.ofNat 3 &&
            (collectFVars {} expression.getAppArgs[2]!).fvarIds.contains argument.fvarId!).isSome then
          throwError "a caller class-valued ordinary parameter changed source elaboration"

end ValueDictionaryRoot

veil module GenericValueSource

type payload
param data : payload
individual value : Nat
after_init { value := 1 }
action restore { value := 1 }
invariant [value_is_one] value = 1

#gen_spec
end GenericValueSource

veil module GenericValueRoot

/-- error: module sorts must be data types, not typeclasses; declare class evidence with param or instantiate -/
#guard_msgs in
isolate s : GenericValueSource
  (payload := OfNat Nat (nat_lit 1))
  (data := (⟨nat_lit 6⟩ : OfNat Nat (nat_lit 1)))

end GenericValueRoot

veil module TypeFamilySource

param family : Nat → Type
individual idle : Bool
after_init { idle := true }
procedure get_one (_x : family 0) { return (1 : Nat) }
action skip { pure () }
invariant [still_idle] idle
#gen_spec
end TypeFamilySource

veil module RejectedClassFamily

/-- error: module type families must have a fixed non-class result type; declare class evidence explicitly -/
#guard_msgs(error, drop warning) in
isolate s : TypeFamilySource (family := fun _ => OfNat Nat (nat_lit 1))

end RejectedClassFamily

veil module DataFamilyComposition

isolate s : TypeFamilySource (family := fun n => Fin (n + 1))
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check Invariants.is_inv

end DataFamilyComposition

veil module DictionaryFieldSource

individual dictionary : OfNat Nat (nat_lit 1)
after_init { dictionary := ⟨nat_lit 2⟩ }
procedure read_dictionary { return (1 : Nat) }
invariant [owns_dictionary] (1 : Nat) = dictionary.ofNat

#gen_spec
end DictionaryFieldSource

veil module ForeignDictionaryFieldRoot

individual callerDictionary : OfNat Nat (nat_lit 1)
isolate fixed : FixedInstanceSource
isolate own : DictionaryFieldSource
procedure read_root_dictionary { return (1 : Nat) }
invariant [root_owns_dictionary] (1 : Nat) = callerDictionary.ofNat

#gen_spec

-- The source's own dictionary and the root's own dictionary both retain
-- their original roles in assertion instance search.
example (st : State FieldAbstractType) :
    @inst_3_own__invariant__owns_dictionary Theory (State FieldAbstractType)
      FieldAbstractType _ _ _ _ default st := by rfl
example (st : State FieldAbstractType) :
    @root_owns_dictionary Theory (State FieldAbstractType)
      FieldAbstractType _ _ _ _ default st := by rfl

open Lean Elab Command in
run_cmd do
  let fixedInfo ← getConstInfo `ForeignDictionaryFieldRoot.inst_5_fixed__procedure__get_one.do
  let some fixedBody := fixedInfo.value? | throwError "missing fixed source body"
  unless fixedBody.getUsedConstants.contains ``instOfNatNat do
    throwError "a foreign field became an implicit source dictionary"
  let invariantInfo ← getConstInfo `ForeignDictionaryFieldRoot.inst_5_fixed__invariant__value_bound
  let some invariantBody := invariantInfo.value? | throwError "missing source invariant body"
  unless invariantBody.getUsedConstants.contains ``instOfNatNat do
    throwError "a foreign field changed source invariant instance search"
  let originalInfo ← getConstInfo `DictionaryFieldSource.read_dictionary.do
  let ownInfo ← getConstInfo `ForeignDictionaryFieldRoot.inst_3_own__procedure__read_dictionary.do
  let some originalBody := originalInfo.value? | throwError "missing original dictionary source body"
  let some ownBody := ownInfo.value? | throwError "missing own dictionary source body"
  unless ownBody.getUsedConstants.contains ``instOfNatNat ==
      originalBody.getUsedConstants.contains ``instOfNatNat do
    throwError "source action dictionary selection changed during specialization"

end ForeignDictionaryFieldRoot
