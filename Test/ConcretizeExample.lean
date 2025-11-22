import Veil
import Veil.Core.Tools.Checker.Concrete.Main

-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit


type node

/- `thread` is not used in this model.
I put it here to explain what we do for the `enum` declaration.
-/
-- enum thread = {T1, T2, T3}

relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool

individual abort_flag : Bool

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

#gen_spec

#check_invariants


--─------------------------------ Prepare Execution (`#gen_exec`) --------------------------
-- #gen_exec
/-
Command `#gen_exec` roughly package all the following commands:
1. `simple_deriving_repr_for' State`
2. `deriving instance Repr for Label`
3. `deriving instance Inhabited for Theory`
4. `deriving_FinOrdToJson_Domain`
5. `specify_FieldConcreteType`
6. `deriving_BEq_FieldConcreteType`
7. `deriving_Hashable_FieldConcreteType`
8. `deriving_rep_FieldRepresentation`
9. `deriving_lawful_FieldRepresentation`
10. `deriving_Inhabited_State`
11. `gen_NextAct`
12. `gen_executable_NextAct`
13. `deriving_Enum_Insts`
-/



/- Prepare some obviously required instance for both`State`, `Theory` and `Label`. -/
simple_deriving_repr_for' State
/- With `Repr` instance, we can show the action label in our frontend interface. -/
deriving instance Repr for Label
deriving instance Inhabited for Theory

/- The domain of each field (e.g., type `node × node × states`) should have `FinEnum`,
`Ord` and `ToJson` instance (used to generate json logs passed to frontend interface).  -/
deriving_FinOrdToJson_Domain

/- Specify the data type of each field in `concrete state`.
By default, `relation` fields are concretized to `TreeSet α`, and
`function` fields are concretized to `TreeMap α β`.
-/
specify_FieldConcreteType

/- Therefore, we need necessary instances before we can run the model checker.
For instance, if a field is concretized to `TreeSet α`, we need to make sure that `α` has
`BEq`, `Hashable`, `Ord` instances.

We also need `lawful` instances for `Veil.LawfulFieldRepresentation` typeclass,
whcih corresponds to Qiyuan's generic field interface laws.
-/
deriving_BEq_FieldConcreteType
deriving_Hashable_FieldConcreteType
deriving_rep_FieldRepresentation
deriving_lawful_FieldRepresentation


/- We need a inhabited instance for the state, which used to generate the _initial state_,
(corresponding to `after_init` action) of the model checking.
-/
deriving_Inhabited_State

/- Generate `initMultiExec` and `nextActMultiExec` (print them to see the details).
Basically, they will be used to be assembled into `initVeilMultiExecM` and `nextVeilMultiExecM`,
which enabled the state transitions.
-/
gen_NextAct
set_option trace.veil.debug true
gen_executable_NextAct

/-
Roughly, `deriving_Enum_Insts` do the following 2 things:
1. For each `enum` type (e.g., `thread`) in veil, derive a inductive datatype with the same name.
2. derive required instances for each enum type, e.g., `FinEnum`, `Ord`, etc.
-/
-- #print thread
deriving_Enum_Insts


--─------------------------------ Model Checking Configuration (`#finitizeTypes`) --------------------------

/-
`#finitizeTypes` package all the following commands:
1. #Concretize
2. deriving_BEqHashable_ConcreteState
3. deriving_toJson_for_state
4. deriving_DecidableProps_state
-/
-- #finitizeTypes (Fin 2), thread


/- Here, user specify which concrete types to be used in the model checking.
The number of given concrete types should be equal to declared types in the veil module.
E.g., here we have two types: `node` and `thread`, so we provide two concrete types:
`Fin 2` and `thread` to replace them respectively.

After that, concrete type `StateConcrete`, `TheoryConcrete`, `LabelConcrete` will be generated,
used for concrete model checking. And we also derive `BEq`, `Hashable`, `ToJson` instances for them.

We can also use `#Concretize thread, thread` here, although it is weird. It means that we concretize
the `node` type to `thread` type.
-/
#Concretize (Fin 5)
-- #Concretize thread, thread
-- 101024 -- 72860ms
-- 4 -- 10256 -- 7783ms
deriving_BEqHashable_ConcreteState
deriving_toJson_for_state
deriving_DecidableProps_state
/-
number (N) | states   | time(ms)
-----------|----------|----------
 2         | 116      | 922
 3         | 1064     | 1477
 4         | 10256    | 8328
 5         | 101024   | 83139
-/

/-
Similar to wiring `.cfg` file in TLA+, user need to specify:
1. `view`: how to view (store) a concrete state (e.g., the hash value will be stored during checking instead of the whole state).
2. `detect_prop`: which property to be detected during model checking
3. `terminationC`: which termination condition to be checked during model checking
4. `cfg`: corresponding to `immutable individual/relation/function` in veil module.
-/
-- def view (st : StateConcrete) := hash st
def view (st : StateConcrete) := st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => safety_0 ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}

def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
#time #eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
-- #eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
-- #html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end TwoPhaseCommit
