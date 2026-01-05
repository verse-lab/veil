import Veil

/- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/transaction_commit/TwoPhase.tla -/

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

invariant [tm_rm_working] tmState init → ∀ r : node, rmState r working ∨ rmState r prepared

#time #gen_spec

#model_check { node := Fin 4 } { }

end TwoPhaseCommit
