module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false

open Veil in
@[wpSimp] public def hiddenStateUpdate {m : Mode} {ρ σ τ : Type}
    [IsSubStateOf τ σ] (update : τ → τ) : VeilM m ρ σ PUnit :=
  modify update

veil module FrameProvider

individual flag : Bool
after_init { flag := true }

#gen_spec
end FrameProvider

veil module FrameConsumer

param provider : FrameProvider
individual localFlag : Bool
after_init { localFlag := true }

-- This is a whole-state Lean helper effect, not a DSL assignment to a
-- module-reference field. The semantic frame must detect it anyway.
action corrupt {
  hiddenStateUpdate (fun (state : State χ) =>
    { state with inst_1_p__field__flag :=
        ((χ_rep State.Label.inst_1_p__field__flag).setSingle () false state.inst_1_p__field__flag) })
}

#gen_spec
end FrameConsumer

veil module SemanticFrameFailure

isolate p : FrameProvider
isolate a : FrameConsumer (provider := p) with p

safety [trivial_safety] True

#gen_spec

/--
error: The following set of actions must preserve the invariant and successfully terminate:
  inst_1_a__procedure__corrupt
    doesNotThrow ... ✅
    frame ... ❌
    trivial_safety ... ✅
-/
#guard_msgs(error, drop info, drop warning) in
#check_action inst_1_a__procedure__corrupt

end SemanticFrameFailure

veil module GuardedFrameConsumer

param provider : FrameProvider
individual initialized : Bool
after_init {
  require initialized
  initialized := false
  ensure ¬initialized
}
action idle { pure () }
invariant [initialization_checked] ¬initialized

#gen_spec
end GuardedFrameConsumer

veil module GuardedFrameInitialization

isolate p : FrameProvider
isolate a : GuardedFrameConsumer (provider := p) with p

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

end GuardedFrameInitialization
