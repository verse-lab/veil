module

public import Veil
public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-! Warn once per mutable hybrid field that still uses a default canonical
instance, including implicit state generation. Enumerable domains, explicitly
configured canonical representations and custom wrapper instances stay quiet. -/

open VeilTest.ActionExecution

veil module HybridFieldWarningDisabledExplicit

set_option veil.warnHybridFields false

function f : Nat → Nat

#guard_msgs in
#gen_state

procedure point_update { f 0 := 7 }
procedure bulk_update { f I := I + 1 }

def initial : State FieldConcreteType := default
def canonical : State FieldConcreteType := ⟨.canonical ⟨fun n => n + 1⟩⟩

-- Exercise the documented transitions with warnings deliberately disabled.
#guard match initial.f with
  | .concrete _ => true
  | .canonical _ => false

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial point_update) fun _ state =>
  match state.f with
  | .concrete _ => true
  | .canonical _ => false

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial bulk_update) fun _ state =>
  match state.f with
  | .canonical cf => cf.inner 1 == 2
  | .concrete _ => false

#guard exactlyOneSuccess (__veil_exec_action% {} {} canonical point_update) fun _ state =>
  match state.f with
  | .canonical cf => cf.inner 0 == 7 && cf.inner 1 == 2
  | .concrete _ => false

end HybridFieldWarningDisabledExplicit

veil module HybridFieldWarningDisabledImplicit

set_option veil.warnHybridFields false

function stored : Nat → Bool

#guard_msgs in
after_init { stored 0 := false }

end HybridFieldWarningDisabledImplicit

-- The option set inside the preceding modules must not suppress this warning.
veil module HybridFieldWarningExplicit

relation present : Nat → Bool
function coverage : Nat → Nat

/--
warning: Field `present` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
---
warning: Field `coverage` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

-- State generation has already warned; later declarations should not repeat it.
#guard_msgs in
after_init {
  present I := false
  coverage I := 0
}

end HybridFieldWarningExplicit

veil module HybridFieldWarningImplicit

function coverage : Nat → Nat

/--
warning: Field `coverage` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
after_init { coverage I := 0 }

#guard_msgs in
action clear (i : Nat) { coverage i := 0 }

end HybridFieldWarningImplicit

veil module HybridFieldWarningEnumerable

type node
relation present : Fin 2 → Bool
function owner : node → node
individual count : Nat

#guard_msgs in
#gen_state

end HybridFieldWarningEnumerable

veil module HybridFieldWarningCanonical

relation present : Nat → Bool
function coverage : Nat → Nat

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#guard_msgs in
#gen_state

end HybridFieldWarningCanonical

veil module HybridFieldWarningMixed

relation present : Nat → Bool
function coverage : Fin 2 → Nat → Nat

veil_set_field_representation relation Veil.CanonicalField

/--
warning: Field `coverage` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningMixed

veil module HybridFieldWarningCustom

function stored : Nat → Bool

-- This model only reaches constant functions, which their value at 0 distinguishes.
local instance (priority := high) : BEq (Veil.CanonicalFieldWrapper [Nat] Bool) where
  beq a b := a.inner 0 == b.inner 0

local instance (priority := high) : Hashable (Veil.CanonicalFieldWrapper [Nat] Bool) where
  hash a := hash (a.inner 0)

#guard_msgs in
#gen_state

after_init { stored I := false }
action fill { stored I := true }
invariant true

#gen_spec

def falseState : State FieldConcreteType := ⟨.canonical ⟨fun _ => false⟩⟩
def trueState : State FieldConcreteType := ⟨.canonical ⟨fun _ => true⟩⟩

#guard (falseState == trueState) == false
#guard hash falseState != hash trueState

-- The custom hash must reach the model checker, not just silence the warning.
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end HybridFieldWarningCustom

veil module HybridFieldWarningCustomHashOnly

function stored : Nat → Bool

local instance (priority := high) : Hashable (Veil.CanonicalFieldWrapper [Nat] Bool) where
  hash a := hash (a.inner 0)

/--
warning: Field `stored` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningCustomHashOnly

veil module HybridFieldWarningCustomBEqOnly

function stored : Nat → Bool

local instance (priority := high) : BEq (Veil.CanonicalFieldWrapper [Nat] Bool) where
  beq a b := a.inner 0 == b.inner 0

/--
warning: Field `stored` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningCustomBEqOnly

veil module HybridFieldWarningCustomParameterized

type node
function stored : node → Nat → Bool

local instance (priority := high) (α : Type) [Inhabited α] :
    BEq (Veil.CanonicalFieldWrapper [α, Nat] Bool) where
  beq a b := a.inner default 0 == b.inner default 0

local instance (priority := high) (α : Type) [Inhabited α] :
    Hashable (Veil.CanonicalFieldWrapper [α, Nat] Bool) where
  hash a := hash (a.inner default 0)

#guard_msgs in
#gen_state

end HybridFieldWarningCustomParameterized

veil module HybridFieldWarningDefaultAliases

function stored : Nat → Bool

-- Merely renaming the defaults does not replace the placeholder behavior.
local instance (priority := high) : BEq (Veil.CanonicalFieldWrapper [Nat] Bool) :=
  Veil.instBEqCanonicalFieldWrapper

local instance (priority := high) : Hashable (Veil.CanonicalFieldWrapper [Nat] Bool) :=
  Veil.instHashableCanonicalFieldWrapper

/--
warning: Field `stored` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningDefaultAliases
