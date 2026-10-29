module

public import Veil

set_option linter.unusedVariables false

/-! Templates imported by the occurrence diagnostics. Their metadata must
survive a Lean module import, rather than existing only in a namespace scope. -/

veil module InstanceSource

type item
param capacity : Nat
relation ready : item → Bool

after_init { ready I := false }
action publish (i : item) { ready i := true }

#gen_spec
end InstanceSource

veil module OtherInstanceSource

type item
param capacity : Nat
relation ready : item → Bool

after_init { ready I := false }
action publish (i : item) { ready i := true }

#gen_spec
end OtherInstanceSource

veil module InstanceConsumer

type item
param capacity : Nat
param source : InstanceSource item capacity
relation seen : item → Bool

after_init { seen I := false }
action observe (i : item) {
  require source.ready i
  seen i := true
}
invariant [seen_ready] ∀ i : item, seen i → source.ready i

#gen_spec
end InstanceConsumer

veil module ForeignWriteConsumer

type item
param capacity : Nat
param source : InstanceSource item capacity
relation seen : item → Bool

after_init { seen I := false }
action overwrite_provider (i : item) {
  source.ready i := false
}

#gen_spec
end ForeignWriteConsumer

veil module UninitializedConsumer

type item
param capacity : Nat
param source : InstanceSource item capacity
relation seen : item → Bool

action observe (i : item) {
  require source.ready i
  seen i := true
}

#gen_spec
end UninitializedConsumer
