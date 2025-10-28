import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
import Mathlib.Data.Fintype.Perm
open Veil
-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit

type node
relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool
individual abort_flag : Bool
immutable individual one : node

#gen_state

after_init {
  vote_yes N := false;
  vote_no N := false;
  alive N := true;
  go_commit N := false;
  go_abort N := false;
  decide_commit N := false;
  decide_abort N := false;
  abort_flag := false
}

action vote1 (n : node) {
  require alive n;
  require ¬vote_no n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_yes n := true
}

action vote2(n: node) {
  require alive n;
  require ¬vote_yes n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_no n := true;
  abort_flag := true;
  decide_abort n := true
}

action fail(n: node) {
  require alive n;
  alive n := false;
  abort_flag := true
}

action go1 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require ∀ N, vote_yes N;
  go_commit N := true
}

action go2 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require exists n, vote_no n ∨ ¬alive n;
  go_abort N := true
}

action commit(n: node) {
  require alive n;
  require go_commit n;
  decide_commit n := true
}

action abort(n: node) {
  require alive n;
  require go_abort n;
  decide_abort n := true
}

safety (decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag)
invariant [manual_1] ¬((¬(alive N) ∧ ¬(abort_flag)))
invariant [manual_2] ¬((¬(abort_flag) ∧ vote_no N))
invariant [manual_3] ¬((¬(abort_flag) ∧ go_abort N))
invariant [manual_4] ¬((¬(go_abort N) ∧ decide_abort N ∧ vote_yes N))
invariant [manual_5] ¬((¬(go_commit N) ∧ decide_commit N))
invariant [manual_6] (N0 ≠ N1) -> ¬((¬(go_commit N0) ∧ go_commit N1))
invariant [manual_7] ¬((¬(vote_yes N) ∧ go_commit N))
invariant [manual_8] ¬((go_commit N ∧ go_abort N))
invariant [trivial_1] ¬(∃n, decide_commit n)

#gen_spec

-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants

section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract

variable [FinEnum node] [Hashable node] [Ord node]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]

def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance


instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')


-- instance :  Ord (IteratedProd' (State.Label.toDomain node State.Label.vote_yes)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node State.Label.vote_no)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node State.Label.alive)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node State.Label.go_commit)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node State.Label.go_abort)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node State.Label.decide_commit)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node State.Label.decide_abort)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance
instance instOrderForComponents' (f : State.Label)
  : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.abort_flag => ((⌞? State.Label.toCodomain ⌟) State.Label.abort_flag)
  | State.Label.vote_yes => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.vote_yes)
  | State.Label.vote_no => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.vote_no)
  | State.Label.alive => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.alive)
  | State.Label.go_commit => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.go_commit)
  | State.Label.go_abort => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.go_abort)
  | State.Label.decide_commit => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.decide_commit)
  | State.Label.decide_abort => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.decide_abort)

instance instReprForComponents [Repr node] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.abort_flag => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.vote_yes =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_yes)
  | State.Label.vote_no =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_no)
  | State.Label.alive =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.alive)
  | State.Label.go_commit =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_commit)
  | State.Label.go_abort =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_abort)
  | State.Label.decide_commit =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_commit)
  | State.Label.decide_abort =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_abort)


instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.abort_flag => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.vote_yes =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_yes)
  | State.Label.vote_no =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_no)
  | State.Label.alive =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.alive)
  | State.Label.go_commit =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_commit)
  | State.Label.go_abort =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_abort)
  | State.Label.decide_commit =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_commit)
  | State.Label.decide_abort =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_abort)

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum node] [Hashable node]
    [Ord node]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum node] [Hashable node]
    [Ord node]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]
  injection_end


instance [Ord node] [FinEnum node]: BEq (Std.TreeSet node) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

#Concretize (Fin 2)


instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.vote_yes) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.vote_no) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.alive) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.go_commit) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.go_abort) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.decide_commit) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.decide_abort) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α]: BEq (FieldConcreteType α State.Label.abort_flag) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance


-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.vote_yes) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.vote_no) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.alive) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.go_commit) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.go_abort) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.decide_commit) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

-- instance [Ord α] [Hashable (Std.TreeSet α)]: Hashable (FieldConcreteType α State.Label.decide_abort) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance

instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
    /- `Hash collision `-/
    -- s.foldl (init := 0) fun acc a => hash (acc, a)
  hash s := hash s.toArray

instance [FinEnum α] [Ord α]: Hashable (FieldConcreteType α State.Label.abort_flag) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

#assembleInsts


instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => manual_1 ρ σ) rd st) := by
  intro rd st
  dsimp [manual_1, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance


instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => trivial_1 ρ σ) rd st) := by
  intro rd st
  dsimp [trivial_1, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def TreeSet.ofList [Ord α] (xs : List α) : Std.TreeSet α :=
  xs.foldl (fun s a => s.insert a) .empty

def mapTreeSet [Ord α ] [Ord β] (f : α → β) (s : Std.TreeSet α)
  : Std.TreeSet β :=
  TreeSet.ofList (s.toList.map f)


def applyPermutate (e : StateConcrete)
  (σ : Equiv.Perm (Veil.IteratedProd' (State.Label.toDomain (Fin 2) State.Label.vote_yes))) : StateConcrete :=
{
  e with
  vote_yes := mapTreeSet (fun p => σ p) e.vote_yes,
  vote_no := mapTreeSet (fun p => σ p) e.vote_no,
  alive := mapTreeSet (fun p => σ p) e.alive,
  go_commit := mapTreeSet (fun p => σ p) e.go_commit,
  go_abort := mapTreeSet (fun p => σ p) e.go_abort,
  decide_commit := mapTreeSet (fun p => σ p) e.decide_commit,
  decide_abort := mapTreeSet (fun p => σ p) e.decide_abort,
  abort_flag := e.abort_flag
}

def st₀ := (((afterInit initVeilMultiExecM {one := 1} default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
#eval st₀


def showPermuted (xs : List α) (σs : List (Equiv.Perm α)) : List (List α) :=
  σs.map (fun σ => xs.map σ)

def permutationDomain := permsOfList (FinEnum.toList (Fin 2))


#eval showPermuted [0, 1, 2] permutationDomain

instance [FinEnum α] [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.vote_yes) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.vote_no) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.alive) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.go_commit) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.go_abort) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.decide_commit) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.decide_abort) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] : Ord (FieldConcreteType α State.Label.abort_flag) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain];
  infer_instance


instance: Ord (StateConcrete) where
  compare a b :=
    compare a.vote_yes b.vote_yes |>.then
    (compare a.vote_no b.vote_no) |>.then
    (compare a.alive b.alive) |>.then
    (compare a.go_commit b.go_commit) |>.then
    (compare a.go_abort b.go_abort) |>.then
    (compare a.decide_commit b.decide_commit) |>.then
    (compare a.decide_abort b.decide_abort) |>.then
    (compare a.abort_flag b.abort_flag)


#eval applyPermutate st₀ (permutationDomain[1])
#reduce Veil.IteratedProd' (State.Label.toDomain (Fin 2) State.Label.vote_yes)


def minOrd? [Ord α] : List α → Option α
  | []      => none
  | x :: xs =>
    some <|
      xs.foldl
        (fun m a => if (compare a m).isLE then a else m)
        x

instance [Hashable StateConcrete] [Ord StateConcrete] [Inhabited StateConcrete] [BEq StateConcrete]: MonadWasSeen StateConcrete (StateT (SearchContext StateConcrete UInt64) Id) where
  wasSeen st := do
    let ctx ← get
    /- `applyPermutate is inconsistent with permutate'`???-/
    let lexicographicalSmall := permutationDomain.map (fun σ => applyPermutate  st σ) |> minOrd?
    let .some smallest := lexicographicalSmall
      |  return (ctx.seen.contains (hash st))
    return (ctx.seen.contains (hash smallest))

instance [Hashable StateConcrete] [Ord StateConcrete] [Inhabited StateConcrete] [BEq StateConcrete]:
MonadWasSeen StateConcrete (StateT (SearchContext StateConcrete StateConcrete) Id) where
  wasSeen st := do
    let ctx ← get
    /- `applyPermutate is inconsistent with permutate'`???-/
    let group := permutationDomain.map (fun σ => applyPermutate st σ)
    let lexicographicalSmall := group |> minOrd?
    let .some smallest := lexicographicalSmall
      |  return (ctx.seen.contains st)
    return (ctx.seen.contains smallest)
    -- return group.any (fun s => ctx.seen.contains s)

#eval permutationDomain.map (fun σ => applyPermutate st₀ σ) |> minOrd?


def view (st : StateConcrete):=
    -- let group := permutationDomain.map (fun σ => applyPermutate st σ)
    -- let lexicographicallySmall := group |> minOrd?
    -- match lexicographicallySmall with
    -- | none => hash st
    -- | .some smallest => hash smallest
    hash st

def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => trivial_1 ρ σ) {one := 1} view).snd
#time #eval modelCheckerResult'.seen.size

/-
- with Symmetric Reduction, `sq` is List
|———|————————|—————————|
| n | states |  time   |
|———|————————|—————————|
| 6 | 896    | 128631ms|
| 5 | 442    | 32659ms |
| 4 | 204    | 271ms   |
| 3 | 87     | 208ms   |
| 2 | 34     | 134ms   |

- with Symmetric Reduction, `sq` is HashSet
|———|————————|—————————|
| n | states |  time   |
|———|————————|—————————|
| 6 | 896    | 124405ms|
| 5 | 442    | 6209ms  |
| 4 | 204    | 589ms   |
| 3 | 87     | 242ms   |
| 2 | 34     | 211ms   |

- without Symmetric Reduction, `sq` is HashSet
|———|————————|—————————|
| n | states |  time   |
|———|————————|—————————|
| 6 |
| 5 | 17018  | 14955ms |
| 4 | 2416   | 3894ms  |
| 3 | 359    | 241ms   |
| 2 | 59     | 185ms   |

-/
-- 41-369ms

def existsRelated' (it : List StateConcrete) : Bool :=
  it.any (fun st1 =>
    it.any (fun st2 =>
      if (st1 == st2) then
        false
      else
        permutationDomain.any (fun σ => (applyPermutate st1 σ == st2))
    )
  )


def findRelatedTriple (it : List StateConcrete) : Option (StateConcrete × StateConcrete) :=
  it.findSome? (fun st1 =>
    it.findSome? (fun st2 =>
      if st1 == st2 then
        none
      else
        permutationDomain.findSome? (fun σ =>
          if applyPermutate st1 σ == st2 then
            some (st1, st2)
          else
            none)))

-- #eval (findRelatedTriple modelCheckerResult'.seen)
-- #eval existsRelated' modelCheckerResult'.seen
-- Without Symmetric Reduction, With Hashing (116 states)
-- Fin3 : 1418ms
-- Fin4 : 11733ms
-- Fin5: 17018 states - 22269ms

-- Without Symmetric Reduction, Without Hashing
-- Fin3: 2182ms
-- Fin4: at least more than 1mins, too much memeory usage
-- Fin4 : 2416 states - 5744ms

-- With Symmetric Reduction, seems succuessfully
-- Fin5: 9813 states - 64774ms
-- Fin5: 442 - 22410ms


-- def permutate' (e : StateConcrete)
--   (σ : Equiv.Perm (Veil.IteratedProd' (State.Label.toDomain (Fin 2) State.Label.vote_yes))) :=
--   let vote_yes' := mapTreeSet (fun p => σ p) e.vote_yes
--   if compare vote_yes' e.vote_yes == .gt then
--     e
--   else
--     let vote_no' := mapTreeSet (fun p => σ p) e.vote_no
--     if compare vote_no' e.vote_no == .gt then
--       e
--     else
--       let alive' := mapTreeSet (fun p => σ p) e.alive
--       if compare alive' e.alive == .gt then
--         e
--       else
--         let go_commit' := mapTreeSet (fun p => σ p) e.go_commit
--         if compare go_commit' e.go_commit == .gt then
--           e
--         else
--           let decide_commit' := mapTreeSet (fun p => σ p) e.decide_commit
--           if compare decide_commit' e.decide_commit == .gt then
--             e
--           else
--             let decide_abort' := mapTreeSet (fun p => σ p) e.decide_abort
--             if compare decide_abort' e.decide_abort == .gt then
--               e
--             else
--               { vote_yes := vote_yes',
--                 vote_no := vote_no',
--                 alive := alive',
--                 go_commit := go_commit',
--                 go_abort := mapTreeSet (fun p => σ p) e.go_abort,
--                 decide_commit := decide_commit',
--                 decide_abort := decide_abort',
--                 abort_flag := e.abort_flag }



end TwoPhaseCommit
