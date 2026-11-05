module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/allocator/SimpleAllocator.tla
-- An allocator that hands out sets of resources to clients, with per-client fairness.
-- SPECIFICATION SimpleAllocator, instance `Clients = {c1,c2}`, `Resources = {r1}`.

veil module SimpleAllocator

type client
type resource

type ResourceSet
instantiate resSet : TSet resource ResourceSet

function unsatisfied : client → ResourceSet
function alloc : client → ResourceSet

#gen_state

-- available == Resources \ (UNION {alloc[c] : c \in Clients})
ghost relation available (r : resource) := ¬ ∃ c : client, r ∈ alloc c

-- Init == unsat = [c \in Clients |-> {}] /\ alloc = [c \in Clients |-> {}]
after_init {
  unsatisfied C := resSet.empty
  alloc C := resSet.empty
}

-- Request(c,S) == unsat[c] = {} /\ alloc[c] = {} /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
action Request (c : client) (S : ResourceSet) {
  require resSet.isEmpty (unsatisfied c)
  require resSet.isEmpty (alloc c)
  require ¬ resSet.isEmpty S
  unsatisfied c := S
}

-- Allocate(c,S) == S # {} /\ S \subseteq available \cap unsat[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \cup S] /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
action Allocate (c : client) (S : ResourceSet) {
  require ¬ resSet.isEmpty S
  require ∀ r : { r // r ∈ S }, available r.val ∧ r.val ∈ unsatisfied c
  alloc c := resSet.union (alloc c) S
  unsatisfied c := resSet.diff (unsatisfied c) S
}

-- Return(c,S) == S # {} /\ S \subseteq alloc[c] /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
action Return (c : client) (S : ResourceSet) {
  require ¬ resSet.isEmpty S
  require ∀ r : { r // r ∈ S }, r.val ∈ alloc c
  alloc c := resSet.diff (alloc c) S
}

-- \/ UNCHANGED vars — the stuttering steps that `[][Next]_vars` allows.
action stutter {
  pure ()
}

-- TypeInvariant == unsat, alloc \in [Clients -> SUBSET Resources] — held by the types here
-- ResourceMutex == \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}
invariant [ResourceMutex]
  ∀ c1 c2 : client, c1 ≠ c2 → resSet.isEmpty (resSet.intersection (alloc c1) (alloc c2))

-- The cfg sets no CHECK_DEADLOCK, so TLC checks for deadlock and reports none.
termination false

-- SimpleAllocator == Init /\ [][Next]_vars /\ \A c \in Clients:
--   WF_vars(Return(c, alloc[c])) /\ SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-- ClientsWillReturn == \A c \in Clients : unsat[c]={} ~> alloc[c]={}
temporal (only := check) [ClientsWillReturn]
  ( (∀ c, (◇ □ (∃ S, ⌜ alloc c = S ⌝ ∧ E(Return c S)))
          → □ ◇ (∃ S, ⌜ alloc c = S ⌝ ∧ T(Return c S)))
  ∧ (∀ c, (□ ◇ (∃ S, E(Allocate c S))) → □ ◇ (∃ S, T(Allocate c S))) )
  → ∀ c, ⌜ resSet.isEmpty (unsatisfied c) ⌝ ↝ ⌜ resSet.isEmpty (alloc c) ⌝

-- ClientsWillObtain == \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]
temporal (only := check) [ClientsWillObtain]
  ( (∀ c, (◇ □ (∃ S, ⌜ alloc c = S ⌝ ∧ E(Return c S)))
          → □ ◇ (∃ S, ⌜ alloc c = S ⌝ ∧ T(Return c S)))
  ∧ (∀ c, (□ ◇ (∃ S, E(Allocate c S))) → □ ◇ (∃ S, T(Allocate c S))) )
  → ∀ c, ∀ r, ⌜ r ∈ unsatisfied c ⌝ ↝ ⌜ r ∈ alloc c ⌝

-- InfOftenSatisfied == \A c \in Clients : []<>(unsat[c] = {})
temporal (only := check) [InfOftenSatisfied]
  ( (∀ c, (◇ □ (∃ S, ⌜ alloc c = S ⌝ ∧ E(Return c S)))
          → □ ◇ (∃ S, ⌜ alloc c = S ⌝ ∧ T(Return c S)))
  ∧ (∀ c, (□ ◇ (∃ S, E(Allocate c S))) → □ ◇ (∃ S, T(Allocate c S))) )
  → ∀ c, □ ◇ ⌜ resSet.isEmpty (unsatisfied c) ⌝

#gen_spec

#model_check
  { client := Fin 2, resource := Fin 1, ResourceSet := OrdList _ }

#temporal_check
  { client := Fin 2, resource := Fin 1, ResourceSet := OrdList _ }

end SimpleAllocator
