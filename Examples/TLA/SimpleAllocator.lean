
import Veil

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
immutable individual Resources : ResourceSet
immutable individual Clients : List client

#gen_state


/- s1 is a subset of s2. -/
ghost relation subset (s1 s2 : ResourceSet) :=
  ∀ r, resSet.contains r s1 → resSet.contains r s2

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
action Request (c : client) {
  -- S \in SUBSET Resources /\ S # {}
  let S :| subset S Resources ∧ resSet.count S > 0
  require resSet.count (unsatisfy c) == 0
  require resSet.count (alloc c) == 0
  unsatisfy c := S
}



-- Allocate(c,S) ==
--   /\ S # {} /\ S \subseteq available \cap unsat[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
--   /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
action Allocate (c : client) {
  /- If we pick a set in non-deterministic way, we will get extra `found states`. -/
  -- let available :| ∀ s, resSet.contains s available → (∀ c', ¬ resSet.contains s (alloc c'))
  let allocsSet := Clients |>.foldl (fun acc c' => resSet.union acc (alloc c')) resSet.empty
  let available := resSet.diff Resources allocsSet
  let S :| subset S available ∧ subset S (unsatisfy c) ∧ resSet.count S > 0
  /- `/\ S \subseteq available \cap unsat[c]` -/
  alloc c := resSet.union (alloc c) S
  unsatisfy c := resSet.diff (unsatisfy c) S
}

-- Return(c,S) ==
--   /\ S # {} /\ S \subseteq alloc[c]
--   /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
--   /\ UNCHANGED unsat
action Return (c : client) {
  /- `/\ S # {} /\ S \subseteq alloc[c]` -/
  let S :| subset S (alloc c) ∧ resSet.count S > 0
  alloc c := resSet.diff (alloc c) S
}

-- Next ==
--   \E c \in Clients, S \in SUBSET Resources :
--      Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

invariant [resource_mutex] ∀ c1 c2 : client, c1 ≠ c2 → ¬(∃s, (resSet.contains s (alloc c1) ∧ resSet.contains s (alloc c2)))
#gen_spec

#model_check
{ client := Fin 3,
  resource := Fin 2,
  ClientsSet := (Std.ExtTreeSet (Fin 3)),
  ResourceSet := (Std.ExtTreeSet (Fin 2)) }
{ Resources := Std.ExtTreeSet.empty.insertMany [0, 1],
  Clients := [0, 1, 2] }

end SimpleAllocator
