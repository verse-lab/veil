module

public import VeilTest.Synthesizer.LockServer
meta import VeilTest.Synthesizer.LockServer
public import VeilTest.Regression.ImportedProofs.Spec

veil module LockServer

-- The certifying run in the defining file already normalized the transition.
/-- transition relation reused -/
#guard_msgs (info, substring := true) in
#updr (expect := invariant)

end LockServer

veil module FlagProofs

-- A user declaration under either reserved name must still stop the search.
theorem ic3_tr_eq_norm : True := True.intro

/-- IC3: FlagProofs.ic3_tr_eq_norm is already declared -/
#guard_msgs (error, substring := true) in
#updr

end FlagProofs
