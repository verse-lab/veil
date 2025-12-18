-- **WARNING**: This file **SHOULD** be put back into the Loom repo!
-- It is here just for easier editing.

import Loom.MonadAlgebras.NonDetT'.ExtractList
import Veil.Frontend.DSL.State.Types

instance (priority := high + 100) {α : Type u} {p : α → Prop} [Veil.Enumeration α] [DecidablePred p] : MultiExtractor.Candidates p where
  find := fun _ => Veil.Enumeration.allValues |>.filter p
  find_iff := by simp ; grind

namespace MultiExtractor

section test

open Lean.Order

class GoodMonadFlatMap' (m' : Type u → Type v) [Monad m'] [MonadFlatMap' m'] where
  op_good : ∀ {α β} (l : List (m' α)) (f : α → m' β),
    MonadFlatMap'.op (l.map (· >>= f)) = MonadFlatMap'.op l >>= f

instance [Monad m'] [inst3 : MonadFlatMap' m'] [GoodMonadFlatMap' m'] : GoodMonadFlatMap' (ReaderT ρ m') where
  op_good := by
    introv ; dsimp +unfoldPartialApp [MonadFlatMap'.op, Function.comp]
    funext r
    have eq1 : (List.map (fun x ↦ x r) (List.map (fun x ↦ x >>= f) l)) =
      List.map (fun x ↦ x >>= (f · r)) (l.map (· r)) := by
      simp [Bind.bind, ReaderT.bind]
    rw [eq1, GoodMonadFlatMap'.op_good] ; rfl

instance [Monad m'] [inst3 : MonadFlatMap' m'] [GoodMonadFlatMap' m'] : GoodMonadFlatMap' (StateT σ m') where
  op_good := by
    introv ; dsimp +unfoldPartialApp [MonadFlatMap'.op, Function.comp]
    funext s
    have eq1 : (List.map (fun x ↦ x s) (List.map (fun x ↦ x >>= f) l)) =
      List.map (fun x ↦ x >>= (fun a => f a.1 a.2)) (l.map (· s)) := by
      simp [Bind.bind, StateT.bind]
    rw [eq1, GoodMonadFlatMap'.op_good] ; rfl

instance [Monad m'] [TsilTCore m'] : GoodMonadFlatMap' (TsilT m') where
  op_good := by
    introv ; simp [MonadFlatMap'.op, Bind.bind]
    -- ok, this could be solved by rewriting using a bunch of theorems, but whatever
    induction l <;> grind

-- the problem is: how to construct the target monad,
-- **based on the structure of the original `NonDetT m α`**?
-- this dependency cannot be skipped in any way; otherwise we cannot
-- obtain any guarantee.

variable
  (κ : Type q)
  (m : Type u → Type v) (m' : Type u → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type u} → (τ → Prop) → Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)

-- TODO `Prop` or `Type _`?
inductive ExtractConstraint : {α : Type u} → (s : NonDetT m α) → m' α → Prop where
  | pure {α : Type u} {x : α} :
    ExtractConstraint (NonDetT.pure x) (inst1.pure x)
  | vis {α β : Type u} (x : m β) (f : β → NonDetT m α) (f' : β → m' α) :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.vis x f) (inst1.bind (inst2.go x) f')
  | pickCont {α : Type u} (τ : Type u) (p : τ → Prop) (f : τ → NonDetT m α) (f' : τ → m' α)
    [instec : ExtCandidates findable κ p] :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.pickCont τ p f)
      (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
        (inst4.log (ExtCandidates.rep findable p (self := instec) x))
        (fun _ => f' x))))
  -- NOTE: without `.{u+1}`, some weird universe level will pop up
  -- NOTE: due to unknown reason, using this instead of `.assume` might cause
  -- unification failure in some cases
  | assumeCont {α : Type u} (p : PUnit.{u+1} → Prop) (f : PUnit.{u+1} → NonDetT m α) (f' : PUnit.{u+1} → m' α)
    [Decidable (p .unit)] :
    (ExtractConstraint (f .unit) (f' .unit)) →
    ExtractConstraint (NonDetT.pickCont PUnit p f)
      (if p .unit then f' .unit else inst3.op [])

theorem ExtractConstraint.assume (p : Prop) [Decidable p] :
  ExtractConstraint κ m m' findOf (MonadNonDet.assume (m := NonDetT m) p)
    (if p then inst1.pure .unit else inst3.op []) := by
  apply ExtractConstraint.assumeCont ; constructor

theorem ExtractConstraint.pickList (p : τ → Prop) [instec : ExtCandidates findable κ p] :
  ExtractConstraint κ m m' findOf (MonadNonDet.pickSuchThat (m := NonDetT m) τ p)
    (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
      (inst4.log (ExtCandidates.rep findable p (self := instec) x))
      (fun _ => inst1.pure x)))) := by
  apply ExtractConstraint.pickCont ; intros ; constructor

theorem ExtractConstraint.liftM [LawfulMonad m'] (x : m α) :
  ExtractConstraint κ m m' findOf (liftM (n := NonDetT m) x) (inst2.go x) := by
  dsimp [_root_.liftM, monadLift, MonadLift.monadLift]
  rw [← bind_pure (MonadFlatMapGo.go x)]
  apply ExtractConstraint.vis ; intros ; constructor

-- TODO this is very very very bad, because just `split` does not split the target mvar. but what is the better way?
theorem ExtractConstraint.ite {α : Type u} (p : Prop)
  (dec : Decidable p)   -- disallow synthesizing
  {s1 : NonDetT m α} {s1' : m' α}
  {s2 : NonDetT m α} {s2' : m' α}
  (h1 : ExtractConstraint κ m m' findOf s1 s1')
  (h2 : ExtractConstraint κ m m' findOf s2 s2') :
  ExtractConstraint κ m m' findOf (@_root_.ite _ p dec s1 s2) (@_root_.ite _ p dec s1' s2') := by
  split ; exact h1 ; exact h2

theorem ExtractConstraint.bind
  [LawfulMonad m']
  [GoodMonadFlatMap' m']
  {α β : Type u} {s : NonDetT m α} {s' : m' α}
  {f : α → NonDetT m β} {f' : α → m' β}
  (hs : ExtractConstraint κ m m' findOf s s')
  (hf : ∀ x, ExtractConstraint κ m m' findOf (f x) (f' x)) :
  ExtractConstraint κ m m' findOf (s >>= f) (inst1.bind s' f') := by
  induction hs generalizing hf with
  | @pure x => simp [Bind.bind, NonDetT.bind] ; exact hf x
  | @vis β x g g' h ih =>
    simp [Bind.bind, NonDetT.bind] ; constructor
    intro y ; apply ih ; assumption
  | @pickCont τ p g g' extcd h ih =>
    simp [Bind.bind, NonDetT.bind]
    rw [← GoodMonadFlatMap'.op_good, List.map_map] ; simp +unfoldPartialApp [Function.comp]
    apply ExtractConstraint.pickCont
    intros ; apply ih ; assumption
  | @assumeCont p g g' _ h ih =>
    simp [Bind.bind, NonDetT.bind]
    have eq : ((if p PUnit.unit then g' PUnit.unit else MonadFlatMap'.op []) >>= f') =
      ((if p PUnit.unit then g' PUnit.unit >>= f' else MonadFlatMap'.op [])) := by
      split <;> try rfl
      rw [← GoodMonadFlatMap'.op_good] ; rfl
    rw [eq] ; clear eq
    -- some very weird unification failure happens here, so need to provide arguments explicitly
    apply ExtractConstraint.assumeCont (p := p) (f' := (fun _ => g' PUnit.unit >>= f'))
    apply ih ; assumption

variable
  [Monad m]
  [CompleteBooleanAlgebra l]
  [MAlgOrdered m l]
  [LawfulMonad m]
  [MAlgOrdered m' l]
  [LawfulMonad m']
  [LawfulMonadPersistentLog κ m' l]
  {α : Type u} (s : NonDetT m α) (s' : m' α)
  (h : ExtractConstraint κ m m' findOf s s')
  (post : α → l)

open AngelicChoice

-- the proofs are taken from `Loom.MonadAlgebras.NonDetT'.ExtractList`

namespace AngelicChoice

include h

theorem extract_list_refines_wp
  [instl : LawfulMonadFlatMapGo m m' l GE.ge]
  [instl2 : LawfulMonadFlatMapSup m' l GE.ge]
  (findOf_sound : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    x ∈ findOf p ec () → p x) :
  wp s' post ≤ wp s post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; apply wp_cons ; aesop (add norm inf_comm)
  | @pickCont τ p f f' extcd h ih =>
    simp [NonDetT.wp_pickCont]
    rename_i extcd
    specialize findOf_sound p extcd
    generalize (findOf p extcd ()) = lis at findOf_sound ⊢
    have tmp := @instl2.sound
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_sound _ hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    split_ifs with h
    · apply le_iSup_of_le .unit ; simp [h] ; apply ih
    · have tmp := @instl2.sound α [] post
      simp [ge_iff_le] at tmp
      rw [tmp] ; simp

theorem wp_refines_extract_list
  [instl : LawfulMonadFlatMapGo m m' l LE.le]
  [instl2 : LawfulMonadFlatMapSup m' l LE.le]
  (findOf_complete : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    p x → x ∈ findOf p ec ()) :
  wp s post ≤ wp s' post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    trans ; (on_goal 2=> apply tmp) ; apply wp_cons ; aesop (add norm inf_comm)
  | @pickCont τ p f f' extcd h ih =>
    simp only [NonDetT.wp_pickCont]
    specialize findOf_complete p extcd
    generalize (findOf p extcd ()) = lis at findOf_complete ⊢
    have tmp := @instl2.sound
    trans ; (on_goal 2=> apply tmp) ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_complete, hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    rintro ⟨⟩ hp ; simp [hp] ; apply ih

omit findOf h in
theorem extract_list_eq_wp
  [instl : LawfulMonadFlatMapGo m m' l Eq]
  [instl2 : LawfulMonadFlatMapSup m' l Eq]
  (h : ExtractConstraint κ m m' (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find) s s') :
  wp s post = wp s' post := by
  apply le_antisymm
  · apply wp_refines_extract_list κ <;> try assumption
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id
  · apply extract_list_refines_wp κ <;> try assumption
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id

end AngelicChoice

macro "extract_list_step'" : tactic =>
  `(tactic|
    first
      -- | eapply $(Lean.mkIdent ``ExtractConstraint.assumeCont)
      | eapply $(Lean.mkIdent ``ExtractConstraint.bind)
      | eapply $(Lean.mkIdent ``ExtractConstraint.liftM)
      | eapply $(Lean.mkIdent ``ExtractConstraint.assume)
      | eapply $(Lean.mkIdent ``ExtractConstraint.pickList)
      | eapply $(Lean.mkIdent ``ExtractConstraint.vis)
      | eapply $(Lean.mkIdent ``ExtractConstraint.pure)
      | eapply $(Lean.mkIdent ``ExtractConstraint.pickCont)
      | eapply $(Lean.mkIdent ``ExtractConstraint.ite)
      -- | split
    )
      -- the order matters!

macro "extract_list_tactic'" : tactic =>
  `(tactic| repeat' (intros; extract_list_step' <;> try dsimp))

set_option linter.unusedVariables false in
def ExtractConstraint.get {α : Type u} {s : NonDetT m α} {s' : m' α}
  (h : ExtractConstraint κ m m' findOf s s' := by extract_list_tactic') : m' α := s'

-- TODO consider where to put these two
def NonDetT.extractList2 {α : Type u} (s : NonDetT m α) {s' : m' α}
  (h : ExtractConstraint κ m m' (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find) s s' := by extract_list_tactic')
  : m' α :=
  ExtractConstraint.get _ _ _ _ h

def NonDetT.extractPartialList2 {α : Type u} (s : NonDetT m α) {s' : m' α}
  (h : ExtractConstraint κ m m' (fun p (ec : ExtCandidates PartialCandidates κ p) => ec.core.find) s s' := by extract_list_tactic')
  : m' α :=
  ExtractConstraint.get _ _ _ _ h

end test

end MultiExtractor
