module

public import Veil

public section

namespace InstantiationHoles

class Collection (elem repr : Type) where
  empty : repr

-- Holes are filled through `@[default_instance]`; a user-defined class opts in per instance.
@[default_instance] instance : Collection α (Array α) where
  empty := #[]

@[veil_decl]
structure Envelope (sender payload : Type) (bound : Nat) where
  source : sender
  body : payload
  slot : Fin (bound + 1)

end InstantiationHoles

open InstantiationHoles

veil module InstantiationHolesContainers

type node
type value
param bound : Nat
enum Status = { ready, waiting }
type NodeSet
type Bag
type Map
type Buffer
type MessageSet

instantiate nodeSet : TSet node NodeSet
instantiate bag : TMultiset value Bag
instantiate map : TMap node value Map
instantiate buffer : Collection node Buffer
instantiate messages : TSet (Envelope node value bound) MessageSet

individual selected : NodeSet

#gen_state

def inferred : Instantiation := __veil_instantiation%
  { node := Fin 2
    value := Bool
    bound := 1
    NodeSet := OrdList _
    Bag := TMapMultiset _
    Map := Std.ExtTreeMap _ _ compare
    Buffer := Array _
    MessageSet := OrdList _ }

example : inferred.NodeSet = OrdList (Fin 2) := rfl
example : inferred.Bag = TMapMultiset Bool := rfl
example : inferred.Map = Std.ExtTreeMap (Fin 2) Bool := rfl
example : inferred.Buffer = Array (Fin 2) := rfl
example : inferred.MessageSet = OrdList (Envelope (Fin 2) Bool 1) := rfl

-- A bare hole picks the class's preferred default container; an explicit head keeps its
-- own container whatever the priority of its default instance.
def inferredBare : Instantiation := __veil_instantiation%
  { node := Fin 2
    value := Bool
    bound := 1
    NodeSet := _
    Bag := _
    Map := _
    Buffer := _
    MessageSet := OrdArray _ }

example : inferredBare.NodeSet = OrdList (Fin 2) := rfl
example : inferredBare.Bag = TMapMultiset Bool := rfl
example : inferredBare.Map = Std.ExtTreeMap (Fin 2) Bool := rfl
example : inferredBare.Buffer = Array (Fin 2) := rfl
example : inferredBare.MessageSet = OrdArray (Envelope (Fin 2) Bool 1) := rfl

-- Comparators left to their `autoParam` default are filled in as well.
def inferredAutoParam : Instantiation := __veil_instantiation%
  { node := Fin 2
    value := Bool
    bound := 1
    NodeSet := Std.ExtTreeSet _
    Bag := TMapMultiset _
    Map := Std.ExtTreeMap _ _
    Buffer := Array _
    MessageSet := Std.ExtTreeSet _ }

example : inferredAutoParam.NodeSet = Std.ExtTreeSet (Fin 2) := rfl
example : inferredAutoParam.Map = Std.ExtTreeMap (Fin 2) Bool := rfl
example : inferredAutoParam.MessageSet = Std.ExtTreeSet (Envelope (Fin 2) Bool 1) := rfl

end InstantiationHolesContainers

-- The default tried first may assign a hole before failing on the output parameter.
-- Its assignments must not survive into the next default.
namespace InstantiationHoles

class ReverseCollection (repr : Type) (elem : outParam Type) where
  empty : repr

@[default_instance] instance [Ord α] : ReverseCollection (OrdList α) α where
  empty := OrdList.empty

@[default_instance high] instance (priority := low) : ReverseCollection (OrdList Bool) Bool where
  empty := OrdList.empty

end InstantiationHoles

veil module InstantiationHolesRollback

type node
type Buffer
instantiate buffer : ReverseCollection Buffer node
individual data : Buffer
#gen_state

def inferred : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := OrdList _ }

example : inferred.Buffer = OrdList (Fin 1) := rfl

end InstantiationHolesRollback

namespace InstantiationHoles

class ElementRepresentation (node : Type) where
  Element : Type

instance : ElementRepresentation (Fin 1) where
  Element := Bool

end InstantiationHoles

veil module InstantiationHolesClassDependency

type node
type Buffer
instantiate representation : ElementRepresentation node
instantiate buffer : Collection representation.Element Buffer
individual data : Buffer
#gen_state

def inferred : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Array _ }

example : inferred.Buffer = Array Bool := rfl

end InstantiationHolesClassDependency

namespace InstantiationHoles

class AmbiguousCollection (elem repr : Type) where
  empty : repr

@[default_instance] instance [Inhabited α] : AmbiguousCollection α (α × Bool) where
  empty := (default, false)

@[default_instance high] instance [Inhabited α] : AmbiguousCollection α (α × Nat) where
  empty := (default, 0)

end InstantiationHoles

veil module InstantiationHolesAmbiguous

type node
type Buffer
instantiate buffer : AmbiguousCollection node Buffer
individual data : Buffer
#gen_state

-- Several matching defaults are not an error: `@[default_instance]` priority decides.
def picked : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Fin 1 × _ }

example : picked.Buffer = (Fin 1 × Nat) := rfl

-- Explicit types retain ordinary instance selection.
example : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Fin 1 × Bool }

end InstantiationHolesAmbiguous

namespace InstantiationHoles

class PlainCollection (elem repr : Type) where
  empty : repr

instance : PlainCollection α (Array α) where
  empty := #[]

end InstantiationHoles

veil module InstantiationHolesNoDefault

type node
type Buffer
instantiate buffer : PlainCollection node Buffer
individual data : Buffer
#gen_state

-- Without a `@[default_instance]` the hole cannot be filled; the obligation is reported
-- at the `instantiate` declaration.
/-- error: typeclass instance problem is stuck -/
#guard_msgs (substring := true) in
example : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Array _ }

end InstantiationHolesNoDefault

namespace InstantiationHoles

class Permission (elem : Type) : Prop where
  allowed : True

class GuardedCollection (elem repr : Type) where
  empty : repr

@[default_instance] instance [Permission α] : GuardedCollection α (Array α) where
  empty := #[]

end InstantiationHoles

veil module InstantiationHolesMissingPremise

type node
type Buffer
param size : Nat
instantiate buffer : GuardedCollection node Buffer
individual data : Buffer
#gen_state

-- A matching instance head cannot bypass its unavailable premise.
/-- error: typeclass instance problem is stuck -/
#guard_msgs (substring := true) in
example : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Array _, size := 1 }

-- Numerals may have pending synthesis, but fully specified types keep the
-- original Instantiation behavior, including unused class assumptions.
example : Instantiation := __veil_instantiation%
  { node := Fin 1, Buffer := Array (Fin 1), size := 1 }

end InstantiationHolesMissingPremise

veil module InstantiationHolesExecution

type node
type NodeSet
instantiate nodeSet : TSet node NodeSet
individual selected : NodeSet
immutable individual limit : Nat
#gen_state

assumption [nonzero] limit > 0

after_init {
  selected := nodeSet.empty
}

action insert (n : node) {
  selected := nodeSet.insert n selected
}

invariant [bounded] nodeSet.count selected ≤ limit
#gen_spec

def executions := __veil_exec_action%
  { node := Fin 1, NodeSet := OrdList _ }
  { limit := 1 }
  { selected := OrdList.empty }
  (insert (0 : Fin 1))

#guard executions.length == 1

#model_check interpreted
  { node := Fin 1, NodeSet := OrdList _ }
  { limit := 1 }
  (maxDepth := 1)
  (sequential := true)
  assumptions_hold_by decide

#model_check compiled
  { node := Fin 1, NodeSet := _ }
  { limit := 1 }
  (maxDepth := 1)
  (sequential := true)

-- No hole, but the comparator is left to its `autoParam`: its tactic must run before the
-- model checker's `TSet` obligation meets the default instances.
#model_check interpreted
  { node := Fin 1, NodeSet := Std.ExtTreeSet (Fin 1) }
  { limit := 1 }
  (maxDepth := 1)
  (sequential := true)
  assumptions_hold_by decide

#guard_msgs(drop info) in
#simulate interpreted
  { node := Fin 1, NodeSet := OrdList _ }
  { limit := 1 }
  (seed := 1) (numTraces := 1) (maxSteps := 1)

end InstantiationHolesExecution
