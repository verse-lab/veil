import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

import Loom.MonadAlgebras.WP.Gen
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.NonDetT'.Basic

namespace MultiExtract

-- compared with `ExtractNonDet` in `NonDetT'`, just have the constructor for `assume` removed
inductive ExtractNonDet (findable : {τ : Type u} -> (τ -> Prop) -> Type w) {m} : {α : Type u} -> NonDetT m α -> Type _ where
  | pure {α} : ∀ (x : α), ExtractNonDet findable (NonDetT.pure x)
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) :
      (∀ y, ExtractNonDet findable (f y)) → ExtractNonDet findable (.vis x f)
  | pickSuchThat {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α)
    {_ : findable p}
     : (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont τ p f)
  -- | assume {α} (p : PUnit -> Prop) (f : PUnit → NonDetT m α) {_ : Decidable (p .unit)} :
  --   (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont PUnit p f)

set_option linter.unusedVariables false in
def ExtractNonDet.bind {findable : {τ : Type u} -> (τ -> Prop) -> Type u} :
  (_ : ExtractNonDet findable x) -> (_ : ∀ y, ExtractNonDet findable (f y)) -> ExtractNonDet findable (x >>= f)
  | .pure x, inst => by
    dsimp [Bind.bind, NonDetT.bind]; exact (inst x)
  | .vis x f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .pickSuchThat _ p f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    assumption; intro y; apply ExtractNonDet.bind <;> solve_by_elim

instance ExtractNonDet.pure' : ExtractNonDet findable (Pure.pure (f := NonDetT m) x) := by
  dsimp [Pure.pure, NonDetT.pure]; constructor

instance ExtractNonDet.liftM (x : m α) :
  ExtractNonDet findable (liftM (n := NonDetT m) x) := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
    intro y; apply ExtractNonDet.pure'

class Candidates {α : Type u} (p : α → Prop) where
  find : Unit → List α
  find_iff : ∀ x, x ∈ find () ↔ p x

class PartialCandidates {α : Type u} (p : α → Prop) where
  find : Unit → List α
  find_then : ∀ x, x ∈ find () → p x

-- class Representable (κ : Type u) (c : {τ : Type u} → (τ → Prop) → Type u) where
--   rep : ∀ {τ} {p : τ → Prop}, c p → τ → κ

-- class ChoiceRepresentable (τ κ : Type u) where
--   rep : τ → κ

class ExtCandidates (c : {τ : Type u} → (τ → Prop) → Type u) (κ : Type w) {α : Type u} (p : α → Prop) where
  core : c p
  rep : α → κ

-- def ExtCandidates (c : {τ : Type u} → (τ → Prop) → Type u) (κ : Type w) : {τ : Type u} → (τ → Prop) → Type _ :=
--   fun {τ} p => (c p × (τ → κ))

-- def ExtCandidates.proj1 {κ : Type u} {c : {τ : Type u} → (τ → Prop) → Type u} {τ : Type u} {p : τ → Prop} :
--   ExtCandidates c κ p → c p := Prod.fst

-- def ExtCandidates.proj2 {κ : Type u} {c : {τ : Type u} → (τ → Prop) → Type u} {τ : Type u} {p : τ → Prop} :
--   ExtCandidates c κ p → τ → κ := Prod.snd

instance PartialCandidates.of_Candidates {α : Type u} (p : α → Prop) [Candidates p] : PartialCandidates p where
  find := Candidates.find p
  find_then := by intro x hx ; rw [Candidates.find_iff] at hx ; exact hx

instance (priority := high) {α : Type u} {p : α → Prop} [FinEnum α] [DecidablePred p] : Candidates p where
  find := fun _ => FinEnum.toList α |>.filter p
  find_iff := by simp [Fintype.complete]

-- FIXME: `PartialCandidates` can be sampled. maybe add one such construction?

-- TODO is this allowed? or we need repetition? maybe just changing `[c p]` into `(c p)` would work
set_option checkBinderAnnotations false in
instance [inst : c p] : ExtCandidates c Unit p where
  core := inst
  rep := fun _ => ()

-- instance [inst : PartialCandidates p] : ExtCandidates PartialCandidates Unit p where
--   core := inst
--   rep := fun _ => ()

set_option checkBinderAnnotations false in
instance (priority := low) [inst : c p] : ExtCandidates c Std.Format p where
  core := inst
  rep := fun _ => "not representable"

set_option checkBinderAnnotations false in
instance {p : α → Prop} [inst : c p] [instr : Repr α] : ExtCandidates c Std.Format p where
  core := inst
  rep := fun a => instr.reprPrec a 0

set_option checkBinderAnnotations false in
instance [inst : c p] : ExtCandidates c (Sigma id) p where
  core := inst
  rep := fun a => ⟨_, a⟩

-- TODO is this allowed? or we need repetition?
set_option checkBinderAnnotations false in
instance ExtractNonDet.pickList {τ : Type u} (p : τ → Prop) [c p] :
  ExtractNonDet c (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
  dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
  assumption; intro y; apply ExtractNonDet.pure

macro "extract_list_step" : tactic =>
  `(tactic|
    first
      | eapply ExtractNonDet.bind
      | eapply ExtractNonDet.pure'
      | eapply ExtractNonDet.liftM
      | eapply ExtractNonDet.pickList
      | split )

macro "extract_list_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_list_step <;> try dsimp))

end MultiExtract
