import Veil

/-## The num of states is the same as TLA+ model.-/

-- import Std.Data.ExtTreeSet.Lemmas
veil module SimpleAllocator
-- ------------------------ MODULE SimpleAllocator -------------------------
-- (***********************************************************************)
-- (* Specification of an allocator managing a set of resources:          *)
-- (* - Clients can request sets of resources whenever all their previous *)
-- (*   requests have been satisfied.                                     *)
-- (* - Requests can be partly fulfilled, and resources can be returned   *)
-- (*   even before the full request has been satisfied. However, clients *)
-- (*   only have an obligation to return resources after they have       *)
-- (*   obtained all resources they requested.                            *)
-- (***********************************************************************)
-- https://github.com/tlaplus/Examples/blob/master/specifications/allocator/SimpleAllocator.tla

-- EXTENDS FiniteSets, TLC

-- CONSTANTS
--   Clients,     \* set of all clients
--   Resources    \* set of all resources
type client
type resource

-- individual Resource : Finset resource
-- immutable relation Clients : client → Bool
-- immutable relation Resources : resource → Bool
-- ASSUME
--   IsFiniteSet(Resources)

type Pool

instantiate setResource : TSet resource Pool
-- VARIABLES
--   unsatisfy,       \* set of all outstanding requests per process
--   alloc        \* set of resources allocated to given process
function unsatisfy : client → Pool
function alloc : client → Pool
-- TypeInvariant ==
--   /\ unsatisfy \in [Clients -> SUBSET Resources]
--   /\ alloc \in [Clients -> SUBSET Resources]

-- -------------------------------------------------------------------------
#gen_state
-- assumption [fixed_clients_set] ∀c, Clients c
-- assumption [finite_resources] ∀s, Resources s


after_init {
  unsatisfy C := setResource.empty
  alloc C := setResource.empty
}

-- Request(c,S) ==
--   /\ unsatisfy[c] = {} /\ alloc[c] = {}
--   /\ S # {} /\ unsatisfy' = [unsatisfy EXCEPT ![c] = S]
--   /\ UNCHANGED alloc
action Request (c : client) (S : Pool) {
  require setResource.count (unsatisfy c) == 0
  require setResource.count (alloc c) == 0
  require setResource.count S > 0
  unsatisfy c := S
}


/- s1 is a subset of s2. -/
ghost relation subset (s1 s2 : Pool) :=
  ∀ r, setResource.contains r s1 → setResource.contains r s2


-- Allocate(c,S) ==
--   /\ S # {} /\ S \subseteq available \cap unsatisfy[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
--   /\ unsatisfy' = [unsatisfy EXCEPT ![c] = @ \ S]
-- available == Resources \ (UNION {alloc[c] : c \in Clients})
action Allocate (c : client) (S : Pool) {
  require setResource.count S > 0
  -- let (available : Finset resource) := Resource \ (⋃ r, (alloc r))
  let available :| ∀ s, setResource.contains s available → (∀ c', ¬ setResource.contains s (alloc c'))
  require subset S available
  alloc c := setResource.union (alloc c) S
  unsatisfy c := setResource.diff (unsatisfy c) S
}


-- Return(c,S) ==
--   /\ S # {} /\ S \subseteq alloc[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
--   /\ UNCHANGED unsatisfy
action Return (c : client) (S : Pool) {
  require setResource.count S > 0
  require subset S (alloc c)
  alloc c := setResource.diff (alloc c) S
}

-- -------------------------------------------------------------------------
-- Next ==
--   \E c \in Clients, S \in SUBSET Resources :
--      Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
-- (* The complete high-level specification. *)
-- SimpleAllocator ==
--   /\ Init /\ [][Next]_vars
--   /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
--   /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-- -------------------------------------------------------------------------

-- ResourceMutex ==
--   \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}
-- ClientsWillReturn ==
--   \A c \in Clients : unsatisfy[c]={} ~> alloc[c]={}
-- ClientsWillObtain ==
--   \A c \in Clients, r \in Resources : r \in unsatisfy[c] ~> r \in alloc[c]
-- InfOftenSatisfied ==
--   \A c \in Clients : []<>(unsatisfy[c] = {})
invariant [resource_mutex] ∀ c1 c2 : client, c1 ≠ c2 → ¬(∃s, (setResource.contains s (alloc c1) ∧ setResource.contains s (alloc c2)))
-- -------------------------------------------------------------------------
-- invariant [trivial_invariant] ∀ c : client, setResource.count (alloc c) ≥ 0
-- -------------------------------------------------------------------------

-- (* The following version states a weaker fairness requirement for the  *)
-- (* clients: resources need be returned only if the entire request has  *)
-- (* been satisfied.                                                     *)

-- SimpleAllocator2 ==
--   /\ Init /\ [][Next]_vars
--   /\ \A c \in Clients: WF_vars(unsatisfy[c] = {} /\ Return(c, alloc[c]))
--   /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

#gen_spec
-- #check_invariants
#model_check { client := Fin 3, resource := Fin 2, Pool := (Std.ExtTreeSet (Fin 2) compare) } {  }
end SimpleAllocator
