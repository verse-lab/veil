import Lean
open Lean

/-! # Veil

Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the Lean 4 proof assistant and provides push-button
verification for transition systems and their properties expressed
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant available when automation falls
short.

This file serves as the root of the `Veil` library. It provides
definitions, options, and attributes that are used throughout the
framework.
-/

/-! ## Trace classes -/

initialize
  registerTraceClass `veil (inherited := true)
  registerTraceClass `veil.info
  registerTraceClass `veil.warning
  registerTraceClass `veil.debug
  registerTraceClass `veil.desugar
  registerTraceClass `veil.wp
  registerTraceClass `veil.timing
  registerTraceClass `veil.extraction
  -- Performance trace classes (integrate with Lean's profiler)
  registerTraceClass `veil.perf (inherited := true)
  registerTraceClass `veil.perf.elaborator
  registerTraceClass `veil.perf.tactic
  registerTraceClass `veil.perf.extract
  registerTraceClass `veil.perf.smt
  registerTraceClass `veil.perf.definition
  registerTraceClass `veil.perf.discharger

/-! ## Options -/

namespace Veil
/-- Veil does some pretty crazy stuff, so we override some of Lean's defaults
when you open a `veil module`. -/
def veilDefaultOptions : List (Name × DataValue) := [
  -- Helpful when elaborating nested procedures.
  (`maxRecDepth, DataValue.ofNat 1024),
  -- Needed because the model checker produces the code for the transition
  -- system (partly) via typeclass inference.
  (`maxHeartbeats, DataValue.ofNat 500000),
  (`synthInstance.maxSize, DataValue.ofNat 4096),
]

register_option veil.printCounterexamples : Bool := {
  defValue := true
  descr := "Print counterexamples (models) when they are found in `#check_invariants`."
}

register_option veil.unfoldGhostRel : Bool := {
  defValue := true
  descr := "If true, `veil_fol` will unfold ghost relations during \
  simplification. This is the behaviour in Veil 1.0. Otherwise, it \
  will use small-scale axiomatization. This option must be set before `#gen_spec`."
}

register_option veil.desugarTactic : Bool := {
  defValue := false
  descr := "If true, Veil-specific tactics will be desugared and the \
  desugared version will be displayed as a suggestion. \
  Note that the formatting of the desugared version depends on **whether \
  the original tactic is placed in isolation** (i.e., whether the lines \
  it spans contain only whitespace characters other than the tactic itself)."
}


register_option veil.violationIsError : Bool := {
  defValue := true
  descr := "If true, violations found by verification or model checking are \
  logged as errors. If false, they are logged as info messages."
}

register_option veil.__modelCheckCompileMode : Bool := {
  defValue := false
  descr := "(INTERNAL ONLY. DO NOT USE.) When true, skip verification-only operations for model checking compilation."
}

inductive VeilSolver : Type where
  | smt
  | grind
  | grindAndSMT
  | custom

instance : Inhabited VeilSolver := ⟨.smt⟩

instance : ToString VeilSolver where
  toString
    | .smt => "smt"
    | .grind => "grind"
    | .grindAndSMT => "grindAndSMT"
    | .custom => "custom"

instance : Lean.KVMap.Value VeilSolver where
  toDataValue s := toString s
  ofDataValue?
    | .ofString "smt" => some .smt
    | .ofString "grind" => some .grind
    | .ofString "grind+smt" => some .grindAndSMT
    | .ofString "custom" => some .custom
    | _ => none

register_option veil.solver : VeilSolver := {
  defValue := .smt
  descr := "Solver strategy used by `veil_solve`.
   - `smt` uses `veil_smt`
   - `grind` uses Lean's `grind`
   - `grind+smt` tries `grind` first, then falls back to `veil_smt`
   - `custom` uses a user-provided `veil_solve` tactic

  For `custom`, define a macro such as
  ```lean
  macro_rules
  | `(tactic| veil_solve) => `(tactic| <your tactic here>)
  ```"
}

register_option veil.smt.finiteModelFind : Bool := {
  defValue := true
  descr := "If true, the SMT solver will use finite model finding mode (finite-model-find). \
  If you work in a decidable fragment, this will tend to speed things up."
}

register_option veil.smt.trust : Bool := {
  defValue := true
  descr := "If true, `veil_smt` trusts unsat results from the SMT solver. \
  If false, `veil_smt` asks the SMT backend to reconstruct Lean proofs."
}

register_option veil.smt.timeout : Nat := {
  defValue := 60
  descr := "Timeout for the SMT solver in seconds. Default is 60 seconds."
}

register_option veil.smt.seed : Nat := {
  defValue := 0
  descr := "Random seed for the SMT solver (cvc5 `seed` and `sat-random-seed`). \
  0 (the default) leaves the solver's own default seed in place; any other \
  value is passed through. Retry attempts (`veil.smt.retries`) perturb this \
  to escape seed-dependent e-matching divergence."
}

register_option veil.smt.retries : Nat := {
  defValue := 1
  descr := "How many times to re-dispatch a VC whose SMT query timed out, \
  before reporting ⏱. Each retry uses a fresh random seed (`veil.smt.seed` = \
  attempt index) and a budget of `veil.smt.retryTimeout` seconds. Retries \
  only fire after a *timeout* (not after `sat`, genuine `unknown`, or \
  errors) and are reported distinctly in the summary so flakiness stays \
  visible. Set to 0 to disable. Must be set before `#gen_spec`."
}

register_option veil.smt.retryTimeout : Nat := {
  defValue := 120
  descr := "Timeout (in seconds) for retry attempts (see `veil.smt.retries`). \
  Timeout-then-fast-success is a seed artifact: such queries either finish \
  quickly under a fresh seed or never, so a short budget avoids burning \
  another full `veil.smt.timeout` on genuinely divergent queries. \
  Must be set before `#gen_spec`."
}

register_option veil.report.slowVCs : Nat := {
  defValue := 10
  descr := "Number of slowest verification conditions to list at the end of \
  `#check_invariants` (ranked by individual discharger time, including failed \
  attempts, which burn the full timeout). Set to 0 to disable the report."
}

register_option veil.report.slowVCsMinMs : Nat := {
  defValue := 5000
  descr := "Minimum discharge time (in milliseconds) for an attempt to appear \
  in the slowest-VCs report; when no attempt qualifies, the report is \
  omitted entirely. The default floor keeps `#check_invariants` output \
  deterministic for fast specifications (e.g. under `#guard_msgs` in tests) \
  while still surfacing the tail on long-running sweeps. Lower it to \
  investigate moderately slow VCs."
}

register_option veil.report.nearTimeoutPercent : Nat := {
  defValue := 50
  descr := "In the slowest-VCs report, flag a discharge attempt as \
  near-timeout (⚠️) when its time exceeds this percentage of \
  `veil.smt.timeout`. Near-timeout VCs are divergence candidates: a small \
  model change (e.g. one added invariant) may push them past the timeout."
}

register_option veil.experimental.wpCompact : Bool := {
  defValue := true
  descr := "Experimental. If true, compact generated `wp_local_eq.pred` definitions by sharing duplicated postcondition branches with `letEq` and exposing abstract-state conditionals field-wise."
}

end Veil
