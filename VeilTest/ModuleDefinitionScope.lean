module

public import Veil

public section

set_option veil.smt.trust false
set_option veil.printCounterexamples false

namespace DefinitionScopeOriginal
abbrev defaultValue : Bool := true
end DefinitionScopeOriginal

open DefinitionScopeOriginal

veil module DefinitionScopeTemplate

individual accepted : Bool
after_init { accepted := defaultValue }
action refresh { accepted := defaultValue }
invariant [accepted_value] accepted

#gen_spec
end DefinitionScopeTemplate

-- This declaration did not exist when the template was elaborated. Looking
-- up its old unqualified identifier during instantiation would change true
-- into false, even if the old namespace/open declarations were restored.
namespace DefinitionScopeTemplate
abbrev defaultValue : Bool := false
end DefinitionScopeTemplate

veil module DefinitionScopeComposition

isolate component : DefinitionScopeTemplate
safety [accepted_value] component.accepted

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check accepted_value.is_inv

end DefinitionScopeComposition

syntax (name := capturedFlag) "captured_flag" : term
macro_rules
  | `(captured_flag) => `(true)

veil module MacroScopeTemplate

individual accepted : Bool
after_init { accepted := captured_flag }
action refresh { accepted := captured_flag }
invariant [accepted_value] accepted

#gen_spec
end MacroScopeTemplate

macro_rules
  | `(captured_flag) => `(false)

-- Establish that the active macro now has different behavior. The recorded
-- module still denotes the program whose code expanded to true.
#guard captured_flag = false

veil module MacroScopeComposition

isolate component : MacroScopeTemplate
safety [accepted_value] component.accepted

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check accepted_value.is_inv

end MacroScopeComposition

-- A nearby module namespace must shadow a root module with the same name.
-- Reference formals resolve in their own definition scope as well.
veil module NamespaceLookupCell
individual value : Bool
after_init { value := true }
action keep { pure () }
invariant [fixed] value
#gen_spec
end NamespaceLookupCell

namespace ModuleLookupScope

veil module NamespaceLookupCell
individual value : Bool
after_init { value := false }
action keep { pure () }
invariant [fixed] value = false
#gen_spec
end NamespaceLookupCell

veil module LookupClient
param provider : NamespaceLookupCell
individual value : Bool
after_init { value := false }
action copy { value := provider.value }
invariant [fixed] value = false
#gen_spec
end LookupClient

veil module LookupComposition
isolate nearby : NamespaceLookupCell
isolate outer : _root_.NamespaceLookupCell
isolate client : LookupClient (provider := nearby) with nearby
safety [bindings] nearby.value = false ∧ outer.value ∧ client.value = false
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check bindings.is_inv
end LookupComposition

end ModuleLookupScope

open ModuleLookupScope

veil module OpenModuleLookupComposition
isolate nearby : ModuleLookupScope.NamespaceLookupCell
isolate client : LookupClient (provider := nearby) with nearby
safety [bindings] nearby.value = false ∧ client.value = false
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check bindings.is_inv
end OpenModuleLookupComposition
