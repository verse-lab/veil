
import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/allocator/SimpleAllocator.tla

veil module SimpleAllocator


type client
type resource

type Pool

instantiate setResource : TSet resource Pool
function unsatisfy : client → Pool
function alloc : client → Pool

#gen_state


after_init {
  unsatisfy C := setResource.empty
  alloc C := setResource.empty
}

action Request (c : client) (S : Pool) {
  require setResource.count (unsatisfy c) == 0
  require setResource.count (alloc c) == 0
  require setResource.count S > 0
  unsatisfy c := S
}

/- s1 is a subset of s2. -/
ghost relation subset (s1 s2 : Pool) :=
  ∀ r, setResource.contains r s1 → setResource.contains r s2

action Allocate (c : client) (S : Pool) {
  require setResource.count S > 0
  -- let (available : Finset resource) := Resource \ (⋃ r, (alloc r))
  let available :| ∀ s, setResource.contains s available → (∀ c', ¬ setResource.contains s (alloc c'))
  require subset S available
  alloc c := setResource.union (alloc c) S
  unsatisfy c := setResource.diff (unsatisfy c) S
}

action Return (c : client) (S : Pool) {
  require setResource.count S > 0
  require subset S (alloc c)
  alloc c := setResource.diff (alloc c) S
}

invariant [resource_mutex] ∀ c1 c2 : client, c1 ≠ c2 → ¬(∃s, (setResource.contains s (alloc c1) ∧ setResource.contains s (alloc c2)))
-- -------------------------------------------------------------------------
-- invariant [trivial_invariant] ∀ c : client, setResource.count (alloc c) ≥ 0
-- -------------------------------------------------------------------------


#gen_spec
-- #check_invariants
#model_check { client := Fin 3, resource := Fin 2, Pool := (Std.ExtTreeSet (Fin 2) compare) } {  }

end SimpleAllocator
