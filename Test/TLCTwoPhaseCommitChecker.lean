import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
import Mathlib.Data.Fintype.Perm
open Veil
-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit
-- CONSTANT RM  \* The set of resource managers
type node --The set of resource managers
-- VARIABLES
enum rmStateType = { working, prepared, committed, aborted }
enum tmStateType = { init, done }
relation rmState (r : node) (st : rmStateType) : Bool
relation tmState (st : tmStateType)
relation tmPrepared (r : node)

--   rmState,       \* rmState[r] is the state of resource manager r.
--   tmState,       \* The state of the transaction manager.
--   tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
--                  \* messages.
--   msgs
--     (***********************************************************************)
--     (* In the protocol, processes communicate with one another by sending  *)
--     (* messages.  For simplicity, we represent message passing with the    *)
--     (* variable msgs whose value is the set of all messages that have been *)
--     (* sent.  A message is sent by adding it to the set msgs.  An action   *)
--     (* that, in an implementation, would be enabled by the receipt of a    *)
--     (* certain message is here enabled by the presence of that message in  *)
--     (* msgs.  For simplicity, messages are never removed from msgs.  This  *)
--     (* allows a single message to be received by multiple receivers.       *)
--     (* Receipt of the same message twice is therefore allowed; but in this *)
--     (* particular protocol, that's not a problem.                          *)
--     (***********************************************************************)
-- vars == <<rmState, tmState, tmPrepared, msgs>>

-- Messages == [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
relation preparedRM (r : node)
individual commitMsg : Bool
individual abortMsg : Bool

#gen_state
-- TPTypeOK ==
--   (*************************************************************************)
--   (* The type-correctness invariant                                        *)
--   (*************************************************************************)
--   /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
--   /\ tmState \in {"init", "done"}
--   /\ tmPrepared \subseteq RM
--   /\ msgs \subseteq Messages

-- TPInit ==
--   (*************************************************************************)
--   (* The initial predicate.                                                *)
--   (*************************************************************************)
--   /\ rmState = [r \in RM |-> "working"]
--   /\ tmState = "init"
--   /\ tmPrepared   = {}
--   /\ msgs = {}
-- -----------------------------------------------------------------------------
after_init {
  rmState R S := S == working
  tmState S := S == init
  tmPrepared R := false

  preparedRM R := false
  commitMsg := false
  abortMsg := false
}

-- (***************************************************************************)
-- (* We now define the actions that may be performed by the processes, first *)
-- (* the TM's actions, then the RMs' actions.                                *)
-- (***************************************************************************)
-- TMRcvPrepared(r) ==
--   (*************************************************************************)
--   (* The TM receives a "Prepared" message from resource manager r.  We     *)
--   (* could add the additional enabling condition r \notin tmPrepared,      *)
--   (* which disables the action if the TM has already received this         *)
--   (* message.  But there is no need, because in that case the action has   *)
--   (* no effect; it leaves the state unchanged.                             *)
--   (*************************************************************************)
--   /\ tmState = "init"
--   /\ [type |-> "Prepared", rm |-> r] \in msgs
--   /\ tmPrepared' = tmPrepared \cup {r}
--   /\ UNCHANGED <<rmState, tmState, msgs>>
action TMRcvPrepared (r : node) {
  require tmState init
  require preparedRM r
  tmPrepared r := true
}

-- TMCommit ==
--   (*************************************************************************)
--   (* The TM commits the transaction; enabled iff the TM is in its initial  *)
--   (* state and every RM has sent a "Prepared" message.                     *)
--   (*************************************************************************)
--   /\ tmState = "init"
--   /\ tmPrepared = RM
--   /\ tmState' = "done"
--   /\ msgs' = msgs \cup {[type |-> "Commit"]}
--   /\ UNCHANGED <<rmState, tmPrepared>>
action TMCommit {
  require tmState init
  require ∀ r : node, tmPrepared r
  tmState S := S == done
  commitMsg := true
}

-- TMAbort ==
--   (*************************************************************************)
--   (* The TM spontaneously aborts the transaction.                          *)
--   (*************************************************************************)
--   /\ tmState = "init"
--   /\ tmState' = "done"
--   /\ msgs' = msgs \cup {[type |-> "Abort"]}
--   /\ UNCHANGED <<rmState, tmPrepared>>
action TMAbort {
  require tmState init
  tmState S := S == done
  abortMsg := true
}


-- RMPrepare(r) ==
--   (*************************************************************************)
--   (* Resource manager r prepares.                                          *)
--   (*************************************************************************)
--   /\ rmState[r] = "working"
--   /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
--   /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
--   /\ UNCHANGED <<tmState, tmPrepared>>
action RMPrepare (r : node) {
  require rmState r working
  rmState r S := S == prepared
  preparedRM r := true
}



-- RMRcvCommitMsg(r) ==
--   (*************************************************************************)
--   (* Resource manager r is told by the TM to commit.                       *)
--   (*************************************************************************)
--   /\ [type |-> "Commit"] \in msgs
--   /\ rmState' = [rmState EXCEPT ![r] = "committed"]
--   /\ UNCHANGED <<tmState, tmPrepared, msgs>>
action RMRcvCommitMsg (r : node) {
  require commitMsg
  rmState r S := S == committed
}


-- RMRcvAbortMsg(r) ==
--   (*************************************************************************)
--   (* Resource manager r is told by the TM to abort.                        *)
--   (*************************************************************************)
--   /\ [type |-> "Abort"] \in msgs
--   /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
--   /\ UNCHANGED <<tmState, tmPrepared, msgs>>
action RMRcvAbortMsg (r : node) {
  require abortMsg
  rmState r S := S == aborted
}

#gen_spec


-- TPNext ==
--   \/ TMCommit \/ TMAbort
--   \/ \E r \in RM :
--        TMRcvPrepared(r) \/ RMPrepare(r)
--          \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
-- -----------------------------------------------------------------------------
-- (***************************************************************************)
-- (* The material below this point is not discussed in Video Lecture 6.  It  *)
-- (* will be explained in Video Lecture 8.                                   *)
-- (***************************************************************************)

-- TPSpec == TPInit /\ [][TPNext]_vars /\ WF_vars(TPNext)
--   (*************************************************************************)
--   (* The complete spec of the Two-Phase Commit protocol.                   *)
--   (*************************************************************************)

-- THEOREM TPSpec => []TPTypeOK
--   (*************************************************************************)
--   (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
--   (* an invariant of the specification.                                    *)
--   (*************************************************************************)
-- -----------------------------------------------------------------------------
-- (***************************************************************************)
-- (* We now assert that the Two-Phase Commit protocol implements the         *)
-- (* Transaction Commit protocol of module TCommit.  The following statement *)
-- (* imports all the definitions from module TCommit into the current        *)
-- (* module.                                                                 *)
-- (***************************************************************************)
-- INSTANCE TCommit

-- THEOREM TPSpec => TCSpec
--   (*************************************************************************)
--   (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
--   (* Commit protocol implements the specification TCSpec of the            *)
--   (* Transaction Commit protocol.                                          *)
--   (*************************************************************************)

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
variable [FinEnum rmStateType] [Hashable rmStateType] [Ord rmStateType]
variable [FinEnum tmStateType] [Hashable tmStateType] [Ord tmStateType]
variable [Ord (node × rmStateType)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))]

variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (node × rmStateType))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (node × rmStateType))))]


def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance instOrderForComponents' (f : State.Label)
  : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


instance (f : State.Label) : Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType f)) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance


-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType State.Label.rmState)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.tmState)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.preparedRM)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.tmPrepared)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.commitMsg)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.abortMsg)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.rmState => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.rmState)
  | State.Label.tmState => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.tmState)
  | State.Label.tmPrepared => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.tmPrepared)
  | State.Label.preparedRM => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.preparedRM)
  | State.Label.commitMsg => ((⌞? State.Label.toCodomain ⌟) State.Label.commitMsg)
  | State.Label.abortMsg => ((⌞? State.Label.toCodomain ⌟) State.Label.abortMsg)


instance instReprForComponents [Repr node] [Repr rmStateType] [Repr tmStateType] (f : State.Label)
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
  | State.Label.commitMsg => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.abortMsg => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.rmState =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.rmState)
  | State.Label.tmState =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.tmState)
  | State.Label.tmPrepared =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.tmPrepared)
  | State.Label.preparedRM =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.preparedRM)



instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.commitMsg => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.abortMsg => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.rmState =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.rmState)
  | State.Label.tmState =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.tmState)
  | State.Label.tmPrepared =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.tmPrepared)
  | State.Label.preparedRM =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.preparedRM)

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum node] [Hashable node]
    [Ord node]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]
    [FinEnum rmStateType] [Hashable rmStateType]
    [Ord rmStateType]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))]
    [FinEnum tmStateType] [Hashable tmStateType]
    [Ord tmStateType]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))]
  injection_end => NextAct'


#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum node] [Hashable node]
    [Ord node]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord node)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord node)))]
    [FinEnum rmStateType] [Hashable rmStateType]
    [Ord rmStateType]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType)))]
    [FinEnum tmStateType] [Hashable tmStateType]
    [Ord tmStateType]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType)))]
  injection_end


deriving_enum_instance_for rmStateType
deriving_enum_instance_for tmStateType


instance : Ord rmStateType where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)

instance : Ord tmStateType where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)


instance : Hashable rmStateType where
  hash s := hash s.toCtorIdx

instance : Hashable tmStateType where
  hash s := hash s.toCtorIdx


instance [Ord α] [FinEnum α]: BEq (Std.TreeSet α) where
  beq s1 s2 :=
    s1.toArray == s2.toArray


#print State


instance :  Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdRmStateType
  intro a b; cases a <;>
    cases b <;> rfl

instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdRmStateType
  decide

instance : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdTmStateType
  intro a b; cases a <;>
    cases b <;> rfl

instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdTmStateType
  decide

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord rmStateType))) := by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdRmStateType
  intro a b; cases a <;>
    cases b <;> simp

instance :  Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord tmStateType))) := by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdTmStateType
  intro a b; cases a <;>
    cases b <;> simp


#Concretize (Fin 4), rmStateType, tmStateType

#print State

instance [FinEnum α] [Ord α] [Hashable α] : BEq (FieldConcreteType α rmStateType tmStateType State.Label.tmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] : BEq (FieldConcreteType α rmStateType tmStateType State.Label.rmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: BEq (FieldConcreteType α rmStateType tmStateType State.Label.tmPrepared) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: BEq (FieldConcreteType α rmStateType tmStateType State.Label.preparedRM) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance  [FinEnum α] [Ord α] [Hashable α]: BEq (FieldConcreteType α rmStateType tmStateType State.Label.commitMsg) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: BEq (FieldConcreteType α rmStateType tmStateType State.Label.abortMsg) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash s := hash s.toArray

instance [FinEnum α] [Ord α] (f : State.Label): BEq (FieldConcreteType α rmStateType tmStateType f) := by
  cases f <;>
    dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'] <;>
    infer_instance

/- ad-hoc -/
instance [FinEnum α] [Ord α] [Hashable α]: Hashable (FieldConcreteType α rmStateType tmStateType State.Label.rmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] : Hashable (FieldConcreteType α rmStateType tmStateType State.Label.tmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: Hashable (FieldConcreteType α rmStateType tmStateType State.Label.tmPrepared) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: Hashable (FieldConcreteType α rmStateType tmStateType State.Label.preparedRM) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: Hashable (FieldConcreteType α rmStateType tmStateType State.Label.commitMsg) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance  [FinEnum α] [Ord α] [Hashable α]: Hashable (FieldConcreteType α rmStateType tmStateType State.Label.abortMsg) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] (f : State.Label): Hashable (FieldConcreteType α rmStateType tmStateType f) := by
  cases f <;>
    dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'] <;>
    infer_instance


    /- `Hash collision `-/
    -- s.foldl (init := 0) fun acc a => hash (acc, a)

instance : BEq StateConcrete where
  beq := fun s1 s2 =>
    s1.rmState == s2.rmState && s1.tmState == s2.tmState && s1.tmPrepared == s2.tmPrepared &&
          s1.preparedRM == s2.preparedRM &&
        s1.commitMsg == s2.commitMsg &&
      s1.abortMsg == s2.abortMsg


#assembleInsts


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def TreeSet.ofList [Ord α] (xs : List α) : Std.TreeSet α :=
  xs.foldl (fun s a => s.insert a) .empty

def mapTreeSet [Ord α ] [Ord β] (f : α → β) (s : Std.TreeSet α)
  : Std.TreeSet β :=
  TreeSet.ofList (s.toList.map f)


def applyPermutate (e : StateConcrete)
  (σ : Equiv.Perm (Fin 4)) : StateConcrete :=
{
  rmState := mapTreeSet (fun (p1, p2) => (σ p1, p2)) e.rmState,
  tmState := e.tmState,
  tmPrepared := mapTreeSet (fun p => σ p) e.tmPrepared,
  preparedRM := mapTreeSet (fun p => σ p) e.preparedRM,
  commitMsg := e.commitMsg,
  abortMsg := e.abortMsg
}

-- relation rmState (r : node) (st : rmStateType) : Bool
-- relation tmState (st : tmStateType)
-- relation tmPrepared (r : node)
-- relation preparedRM (r : node)
-- individual commitMsg : Bool
-- individual abortMsg : Bool


def st₀ := (((afterInit initVeilMultiExecM {} default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
#eval st₀


def showPermuted (xs : List α) (σs : List (Equiv.Perm α)) : List (List α) :=
  σs.map (fun σ => xs.map σ)

def permutationDomain := permsOfList (FinEnum.toList (Fin 4))


#eval showPermuted [0, 1, 2, 3, 4] permutationDomain

instance [FinEnum α] [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

-- instance [Hashable α] [BEq α] [Ord α]: Ord (Std.HashSet α) where
--   compare s1 s2 := compare s1.toArray s2.toArray

instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.rmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

#print State
instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.tmState) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.tmPrepared) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.preparedRM) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.commitMsg ) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α]:  Ord (FieldConcreteType α rmStateType tmStateType State.Label.abortMsg ) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


/-
<<Symmetric Reduction>>

1. Make sure that each state can be ordered, i.e.,,
   we give an Ord instance so we can compare them.

2. For every state, apply all the permutations in a given symmetry domain
   to generate a set of equivalent (symmetric) states.

3. Pick the smallest one among them according to the ordering
   and use that as the state’s `fingerprint`


[Note]: maybe require making appropriate trade-offs.

The current approach actually computes all permuted states from each reachable state
by performing the permutations, but storing only a (deterministically) selected representative.
This assumes that `building such steps through permutations` is faster than `reaching it through a next step`.
-/
instance: Ord StateConcrete where
  compare a b :=
    compare a.rmState b.rmState |>.then
    (compare a.tmState b.tmState) |>.then
    (compare a.preparedRM b.preparedRM) |>.then
    (compare a.commitMsg b.commitMsg) |>.then
    (compare a.abortMsg b.abortMsg)


def minOrd? [Ord α] : List α → Option α
  | []      => none
  | x :: xs =>
    let cmpf := (fun m a => if (compare a m).isLE then a else m)
    some <| xs.foldl cmpf x


/- `View` used to implement the symmetric reduction.
When the function is defined as `id`, then model checker
will store and show all the original states, rather than hash value.
-/
def view (st : StateConcrete):=
    let group := permutationDomain.map (fun σ => applyPermutate st σ)
    let lexicographicallySmall := group |> minOrd?
    match lexicographicallySmall with
    | none => hash st
    | .some smallest => hash smallest



def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => true) {} view).snd
#time #eval modelCheckerResult'


/-
- with Symmetric Reduction
|———|————————|—————————|
| n | states |  time   |
|———|————————|—————————|
| 6 | 1187   | 257305ms| ! Worse too
| 5 | 512    | 11245ms | ! Worse than non-symmetric reduction
| 4 | 211    | 736ms   |
| 3 | 85     | 259ms   |
| 2 | 32     | 152ms   |

- Non-Symmetric Reduction
|———|————————|—————————|
| n | states |  time   |
|———|————————|—————————|
| 6 | 47449  | 23486ms |
| 5 | 8051   | 4110ms  |
| 4 | 1393   | 591ms   |
| 3 | 251    | 293ms   |
| 2 | 49     | 205ms   |

-/

end TwoPhaseCommit
