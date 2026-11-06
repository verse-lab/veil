module

public import Veil
public import Veil.Core.Tools.LivenessMC.LivenessMC
public meta import Veil.Core.Tools.LivenessMC.LivenessMC
public meta import Veil.Core.Tools.LivenessMC.Report
public meta import Veil.Core.Tools.LivenessMC.Benchmarking
import Lasso

set_option veil.deferVCGeneration true

/-! # Nested fairness: a fairness assumption TLC has to build a tableau for

    Three request-processing servers. Each sits idle until it accepts a request, processes it, and
    emits a reply, and from the receiving or working stage it may instead abort back to idle.

    Q: does server 0 emit infinitely often?
    - No: every server can accept-then-abort forever and never emit.

    The assumption that fixes it is that each server's whole cycle completes infinitely often,
    `□◇(recv i ∧ ◇(work i ∧ ◇emit i))`. This is detected by Veil/Lasso as a fairness and
    specialized fairness handling is applied.

    Since this is not literally `□◇prop`, it is not detected as a fairness by TLC, so TLC is much slower here.
    The above formula can be flattened by applying this rule: `□◇(φ ∧ ◇ψ) ≡ □◇ φ ∧ □◇ ψ`, such that TLC
    can detect it. The difference is therefore only sensitivity of the tools to formula syntax.
-/

veil module NestedServers

abbrev Server := Fin 3

relation recv : Server -> Bool
relation work : Server -> Bool
relation emit : Server -> Bool

#gen_state

after_init {
  recv S := false
  work S := false
  emit S := false
}

-- idle is all three false, so `accept` is the only move out of it
action accept (s : Server) {
  require recv s = false ∧ work s = false ∧ emit s = false
  recv s := true
}
action process (s : Server) {
  require recv s = true
  recv s := false
  work s := true
}
action send (s : Server) {
  require work s = true
  work s := false
  emit s := true
}
action finish (s : Server) {
  require emit s = true
  emit s := false
}
-- the abort edge, which is what makes `□◇recv` too weak an assumption
action abort (s : Server) {
  require recv s = true ∨ work s = true
  recv s := false
  work s := false
}

safety [oneStage] ¬(recv 0 = true ∧ work 0 = true)

-- False: every server can accept then abort forever.
temporal [server0Emits] □ ◇ ⌜ emit 0 = true ⌝

-- False too: the accept-then-abort loop satisfies it and never emits.
temporal [server0EmitsWeak]
  (□ ◇ ⌜ recv 0 = true ⌝) → □ ◇ ⌜ emit 0 = true ⌝

-- True: each server's whole cycle completes infinitely often.
temporal [server0EmitsFair]
  ( (□ ◇ (⌜ recv 0 = true ⌝ ∧ ◇ (⌜ work 0 = true ⌝ ∧ ◇ ⌜ emit 0 = true ⌝)))
  ∧ (□ ◇ (⌜ recv 1 = true ⌝ ∧ ◇ (⌜ work 1 = true ⌝ ∧ ◇ ⌜ emit 1 = true ⌝)))
  ∧ (□ ◇ (⌜ recv 2 = true ⌝ ∧ ◇ (⌜ work 2 = true ⌝ ∧ ◇ ⌜ emit 2 = true ⌝))) )
  → □ ◇ ⌜ emit 0 = true ⌝

#gen_spec
#gen_executable

--#temporal_check [server0EmitsFair] compiled {}
--#temporal_check [server0EmitsWeak] compiled {}
--#temporal_check [server0Emits] compiled {}

end NestedServers
