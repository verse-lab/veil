module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/allocator/SimpleAllocator.tla
-- Resource allocator with per-client weak and strong fairness; 2 clients, 1 resource.

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

-- Fixed representatives, since `liveness` atoms can't quantify (∀/∃) over abstract sorts.
immutable individual c0 : client
immutable individual c1 : client
immutable individual r0 : resource

#gen_state

/- s1 is a subset of s2. -/
ghost relation subset (s1 s2 : ResourceSet) :=
  ∀ r, resSet.contains r s1 → resSet.contains r s2

-- Init == unsat = [c |-> {}] /\ alloc = [c |-> {}]
after_init {
  unsatisfy C := resSet.empty
  alloc C := resSet.empty
}

-- Request(c,S) == unsat[c] = {} /\ alloc[c] = {} /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
action Request (c : client) {
  let S :| subset S Resources ∧ resSet.count S > 0
  require resSet.count (unsatisfy c) == 0
  require resSet.count (alloc c) == 0
  unsatisfy c := S
}

-- Allocate(c,S) == S # {} /\ S \subseteq available \cap unsat[c] /\ alloc' = ... /\ unsat' = ...
-- Split per client: `E`/`T` cannot name an instantiation, so the instantiation is baked into the
-- action and the label becomes nullary. `let c := cN` leaves the body verbatim. See the header.
action Allocate_c0 {
  let c := c0
  let allocsSet := Clients |>.foldl (fun acc c' => resSet.union acc (alloc c')) resSet.empty
  let available := resSet.diff Resources allocsSet
  let S :| subset S available ∧ subset S (unsatisfy c) ∧ resSet.count S > 0
  alloc c := resSet.union (alloc c) S
  unsatisfy c := resSet.diff (unsatisfy c) S
}

action Allocate_c1 {
  let c := c1
  let allocsSet := Clients |>.foldl (fun acc c' => resSet.union acc (alloc c')) resSet.empty
  let available := resSet.diff Resources allocsSet
  let S :| subset S available ∧ subset S (unsatisfy c) ∧ resSet.count S > 0
  alloc c := resSet.union (alloc c) S
  unsatisfy c := resSet.diff (unsatisfy c) S
}

-- Return(c,S) == S # {} /\ S \subseteq alloc[c] /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
-- Split per client, as `Allocate` above.
action Return_c0 {
  let c := c0
  let S :| subset S (alloc c) ∧ resSet.count S > 0
  alloc c := resSet.diff (alloc c) S
}

action Return_c1 {
  let c := c1
  let S :| subset S (alloc c) ∧ resSet.count S > 0
  alloc c := resSet.diff (alloc c) S
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

-- ResourceMutex == \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}
invariant [resource_mutex] ∀ c1 c2 : client, c1 ≠ c2 → (resSet.intersection (alloc c1) (alloc c2) = resSet.empty)

-- ClientsWillObtain == \A c, r : r \in unsat[c] ~> r \in alloc[c] (c0/r0 case only, by symmetry).
-- Not checked on TLC.
temporal [clientsWillObtain]
  □ (⌜ resSet.contains r0 (unsatisfy c0) ⌝ → ◇ ⌜ resSet.contains r0 (alloc c0) ⌝)

-- SimpleAllocator == Init /\ [][Next]_vars /\ \A c : WF_vars(Return(c, alloc[c]))
--                                          /\ \A c : SF_vars(\E S \in SUBSET Resources : Allocate(c, S)),
-- which is what TLC checks every property against, so every `…Fair` property below carries all four
-- conjuncts. SF_v(A) = □◇E(A) → □◇T(A) (no outer □) — not □(◇E→◇T), which is strictly stronger
-- There is no WF_vars(Next): a behaviour may stutter forever, so there is no
-- `□◇¬T(stutter)` conjunct. With one resource every Return(c, S) is Return(c, alloc[c]), so
-- `T(Return_cN)` is exact here (it would be weaker with two).
temporal [clientsWillObtainFair]
  ((□ (◇ ¬ E(Return_c0) ∨ ◇ T(Return_c0)))
   ∧ (□ (◇ ¬ E(Return_c1) ∨ ◇ T(Return_c1)))
   ∧ ((□ ◇ E(Allocate_c0)) → (□ ◇ T(Allocate_c0)))
   ∧ ((□ ◇ E(Allocate_c1)) → (□ ◇ T(Allocate_c1))))
  → ((□ (⌜ resSet.contains r0 (unsatisfy c0) ⌝ → ◇ ⌜ resSet.contains r0 (alloc c0) ⌝)) ∧
     (□ (⌜ resSet.contains r0 (unsatisfy c1) ⌝ → ◇ ⌜ resSet.contains r0 (alloc c1) ⌝)))

-- ClientsWillReturn == \A c \in Clients : unsat[c]={} ~> alloc[c]={}
-- Not checked on TLC.
temporal [clientsWillReturn]
  (□ (⌜ resSet.count (unsatisfy c0) = 0 ⌝ → ◇ ⌜ resSet.count (alloc c0) = 0 ⌝)) ∧
  (□ (⌜ resSet.count (unsatisfy c1) = 0 ⌝ → ◇ ⌜ resSet.count (alloc c1) = 0 ⌝))

temporal [clientsWillReturnFair]
  ((□ (◇ ¬ E(Return_c0) ∨ ◇ T(Return_c0)))
   ∧ (□ (◇ ¬ E(Return_c1) ∨ ◇ T(Return_c1)))
   ∧ ((□ ◇ E(Allocate_c0)) → (□ ◇ T(Allocate_c0)))
   ∧ ((□ ◇ E(Allocate_c1)) → (□ ◇ T(Allocate_c1))))
  → ((□ (⌜ resSet.count (unsatisfy c0) = 0 ⌝ → ◇ ⌜ resSet.count (alloc c0) = 0 ⌝)) ∧
     (□ (⌜ resSet.count (unsatisfy c1) = 0 ⌝ → ◇ ⌜ resSet.count (alloc c1) = 0 ⌝)))

-- InfOftenSatisfied == \A c \in Clients : []<>(unsat[c] = {})
-- Not checked on TLC.
temporal [infOftenSatisfied]
  (□ ◇ ⌜ resSet.count (unsatisfy c0) = 0 ⌝) ∧
  (□ ◇ ⌜ resSet.count (unsatisfy c1) = 0 ⌝)

temporal [infOftenSatisfiedFair]
  ((□ (◇ ¬ E(Return_c0) ∨ ◇ T(Return_c0)))
   ∧ (□ (◇ ¬ E(Return_c1) ∨ ◇ T(Return_c1)))
   ∧ ((□ ◇ E(Allocate_c0)) → (□ ◇ T(Allocate_c0)))
   ∧ ((□ ◇ E(Allocate_c1)) → (□ ◇ T(Allocate_c1))))
  → ((□ ◇ ⌜ resSet.count (unsatisfy c0) = 0 ⌝) ∧ (□ ◇ ⌜ resSet.count (unsatisfy c1) = 0 ⌝))

#gen_spec

def theory0 : Theory (Fin 2) (Fin 1) (Std.ExtTreeSet (Fin 1) compare) (Std.ExtTreeSet (Fin 2) compare) :=
  { Resources := Std.ExtTreeSet.empty.insertMany [0],
    Clients := [0, 1],
    c0 := 0,
    c1 := 1,
    r0 := 0 }

#temporal_check [clientsWillObtainFair] [clientsWillReturnFair] [infOftenSatisfiedFair] compiled { client := (Fin 2), resource := (Fin 1), ResourceSet := (Std.ExtTreeSet (Fin 1) compare), ClientsSet := (Std.ExtTreeSet (Fin 2) compare) } theory0 (route := .fair)

end SimpleAllocator
