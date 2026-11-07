module

public import Veil

/-! Warn once per mutable hybrid field that still uses a default canonical
instance, including implicit state generation. Enumerable domains, explicitly
configured canonical representations and custom wrapper instances stay quiet. -/

veil module HybridFieldWarningExplicit

relation present : Nat → Bool
function coverage : Nat → Nat

/--
warning: Field `present` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
---
warning: Field `coverage` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
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
warning: Field `coverage` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
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
warning: Field `coverage` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
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
warning: Field `stored` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningCustomHashOnly

veil module HybridFieldWarningCustomBEqOnly

function stored : Nat → Bool

local instance (priority := high) : BEq (Veil.CanonicalFieldWrapper [Nat] Bool) where
  beq a b := a.inner 0 == b.inner 0

/--
warning: Field `stored` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
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
warning: Field `stored` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
-/
#guard_msgs in
#gen_state

end HybridFieldWarningDefaultAliases
