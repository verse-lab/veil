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
#gen_exec
#finitizeTypes (Fin 5), rmStateType, tmStateType

def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}


def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
#eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end TwoPhaseCommit
