module

public import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/allocator/SimpleAllocator.tla

veil module SimpleAllocator

type client
type resource

type ResourceSet
type ClientsSet
instantiate resSet : TSet resource ResourceSet
instantiate cSet : TSet client ClientsSet

function unsatisfy : client → ResourceSet
function alloc : client → ResourceSet

#gen_state

/-
ghost function available : ResourceSet :=
  let allocsSet := Clients.foldl (fun acc c => resSet.union acc (alloc c)) resSet.empty
  resSet.diff Resources allocsSet
-/

-- NOTE: This is not very easy to express as a function that
-- computes a set, but as a relation it is straightforward.
ghost relation availableRel (r : resource) :=
  ¬ ∃ c : client, r ∈ alloc c

-- /- s1 is a subset of s2. -/
-- ghost relation subset (s1 s2 : ResourceSet) :=
--   ∀ r, resSet.contains r s1 → resSet.contains r s2

-- Init ==
--   /\ unsat = [c \in Clients |-> {}]
--   /\ alloc = [c \in Clients |-> {}]
after_init {
  unsatisfy C := resSet.empty
  alloc C := resSet.empty
}

-- Request(c,S) ==
--   /\ unsat[c] = {} /\ alloc[c] = {}
--   /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
--   /\ UNCHANGED alloc
action Request (c : client) (S : ResourceSet) {
  -- S \in SUBSET Resources /\ S # {}
  require resSet.isEmpty (unsatisfy c)
  require resSet.isEmpty (alloc c)
  require ¬ resSet.isEmpty S
  unsatisfy c := S
}

-- Allocate(c,S) ==
--   /\ S # {} /\ S \subseteq available \cap unsat[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
--   /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
action Allocate (c : client) (S : ResourceSet) {
  require ¬ resSet.isEmpty S
  require ∀ (e : { e // e ∈ S }), availableRel e.val ∧ e.val ∈ (unsatisfy c)
  alloc c := resSet.union (alloc c) S
  unsatisfy c := resSet.diff (unsatisfy c) S
}

-- Return(c,S) ==
--   /\ S # {} /\ S \subseteq alloc[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
--   /\ UNCHANGED unsat
action Return (c : client) (S : ResourceSet) {
  require ¬ resSet.isEmpty S
  require ∀ (e : { e // e ∈ S }), e.val ∈ alloc c
  alloc c := resSet.diff (alloc c) S
}

-- Next ==
--   \E c \in Clients, S \in SUBSET Resources :
--      Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
-- ResourceMutex ==
--   \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}
invariant [resource_mutex] ∀ c1 c2 : client, c1 ≠ c2 → (resSet.isEmpty <| resSet.intersection (alloc c1) (alloc c2))
#gen_spec

#model_check interpreted
{ client := Fin 2,
  resource := Fin 2,
  ClientsSet := OrdList _,
  ResourceSet := OrdList _ }

end SimpleAllocator
