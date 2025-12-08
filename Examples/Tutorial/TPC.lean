import Veil

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

relation preparedRM (r : node)
individual commitMsg : Bool
individual abortMsg : Bool

#gen_state

after_init {
  rmState R S := S == working
  tmState S := S == init
  tmPrepared R := false

  preparedRM R := false
  commitMsg := false
  abortMsg := false
}


action TMRcvPrepared (r : node) {
  require tmState init
  require preparedRM r
  tmPrepared r := true
}


action TMCommit {
  require tmState init
  require ∀ r : node, tmPrepared r
  tmState S := S == done
  commitMsg := true
}


action TMAbort {
  require tmState init
  tmState S := S == done
  abortMsg := true
}



action RMPrepare (r : node) {
  require rmState r working
  rmState r S := S == prepared
  preparedRM r := true
}



action RMRcvCommitMsg (r : node) {
  require commitMsg
  rmState r S := S == committed
}



action RMRcvAbortMsg (r : node) {
  require abortMsg
  rmState r S := S == aborted
}

#gen_spec


#gen_exec

#finitize_types (Fin 7), rmStateType, tmStateType

#set_theory {}

set_option trace.veil.debug true
#run_checker (fun a b => true)
-- def modelCheckerResult :=
--       (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun rd st => True)
--           concreteTheory (hash)).snd

-- #eval modelCheckerResult.seen.size
-- #time #eval spaceSize modelCheckerResult

end TwoPhaseCommit
