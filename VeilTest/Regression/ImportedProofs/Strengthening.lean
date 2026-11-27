module

public import VeilTest.Synthesizer.LockServer
meta import VeilTest.Synthesizer.LockServer

veil module LockServer
/-- info: Add the strengthening invariants before `#gen_spec` in `VeilTest.Synthesizer.LockServer`. -/
#guard_msgs (info, substring := true) in
#updr (expect := invariant)
end LockServer
