module

public import VeilTest.ModuleInstanceHelper

set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module InstanceBindingDiagnostics

type item

/-- error: unknown or unfinished Veil module MissingInstanceTemplate; finish its definition with #gen_spec -/
#guard_msgs in
isolate missing_template : MissingInstanceTemplate

/-- error: missing binding for module parameter capacity -/
#guard_msgs in
isolate missing_parameter : InstanceSource (item := item)

/-- error: unknown parameter surprise of module InstanceSource -/
#guard_msgs in
isolate unknown_parameter : InstanceSource (item := item) (capacity := 2) (surprise := 0)

/-- error: duplicate binding for parameter capacity -/
#guard_msgs in
isolate duplicate_parameter : InstanceSource (item := item) (capacity := 2) (capacity := 3)

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat
-/
#guard_msgs in
isolate bad_value_type : InstanceSource (item := item) (capacity := true)

isolate source : InstanceSource (item := item) (capacity := 2)
isolate other : OtherInstanceSource (item := item) (capacity := 2)

/-- error: duplicate isolate name source -/
#guard_msgs in
isolate source : InstanceSource (item := item) (capacity := 2)

/-- error: unknown isolate dependency absent; dependencies must precede their users -/
#guard_msgs in
isolate absent_support : InstanceSource (item := item) (capacity := 2) with absent

/-- error: module reference source requires existing isolate source in the `with` list -/
#guard_msgs in
isolate missing_support : InstanceConsumer (item := item) (capacity := 2) (source := source)

/-- error: module reference source expects InstanceSource, got OtherInstanceSource -/
#guard_msgs in
isolate wrong_provider : InstanceConsumer (item := item) (capacity := 2) (source := other) with other

/-- error: incompatible binding for capacity in module reference source -/
#guard_msgs in
isolate wrong_capacity : InstanceConsumer (item := item) (capacity := 3) (source := source) with source

/-- error: incompatible binding for item in module reference source -/
#guard_msgs in
isolate wrong_sort : InstanceConsumer (item := Bool) (capacity := 2) (source := source) with source

end InstanceBindingDiagnostics

veil module SharedInstanceProvider

type item

isolate source : InstanceSource (item := item) (capacity := 2)
isolate left : InstanceConsumer (item := item) (capacity := 2) (source := source) with source
isolate right : InstanceConsumer (item := item) (capacity := 2) (source := source) with source

safety [both_backed] ∀ i : item, (left.seen i ∨ right.seen i) → source.ready i

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

#check both_backed.is_inv

-- Dependency references reuse source; each consumer contributes only seen.
run_cmd do
  let mod ← Veil.getCurrentModule
  unless mod.signature.size == 3 do
    throwError "a dependency reference allocated duplicate mutable state"
  unless mod.instances.size == 3 do
    throwError "expected exactly three concrete instances"
  unless mod.actions.size == 3 do
    throwError "expected exactly three independently scheduled action families"

end SharedInstanceProvider

veil module ForeignInstanceWrite

type item

isolate source : InstanceSource (item := item) (capacity := 2)
isolate writer : ForeignWriteConsumer (item := item) (capacity := 2) (source := source) with source

/-- error: module reference fields are read-only; an instance can write only its own state -/
#guard_msgs in
#gen_spec

end ForeignInstanceWrite

veil module MissingInstanceInitializer

type item

isolate source : InstanceSource (item := item) (capacity := 2)
isolate consumer : UninitializedConsumer (item := item) (capacity := 2) (source := source) with source

/-- error: module instance consumer has no after_init block; every instance must initialize its state -/
#guard_msgs in
#gen_spec

end MissingInstanceInitializer
