module

public import Lean.Data.Options
import Lean.Util.Trace

public section
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

register_option veil.extract.shareValueLets : Bool := {
  defValue := true
  descr := "If true (the default), extraction keeps ordinary value `let`s shared \
  in the extracted term instead of zeta-reducing them. Sharing makes the extracted \
  term smaller but costs extraction time, and the compiler's `pullInstances` and \
  `cse` passes run before its first `simp` and recover the sharing anyway. Join \
  points are shared either way; inlining those is exponential in the number of \
  sequential branches and no later pass can undo it."
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

register_option veil.experimental.wpCompact : Bool := {
  defValue := true
  descr := "Experimental. If true, compact generated `wp_local_eq.pred` definitions by sharing duplicated postcondition branches with `letEq` and exposing abstract-state conditionals field-wise."
}

register_option veil.deferVCGeneration : Bool := {
  defValue := false
  descr := "If true, procedures and actions declared while this option is set do not generate their verification definitions, \
  and `#gen_spec` run while it is set generates no verification conditions, so it also skips the assertion-failure (`doesNotThrow`) checks. \
  The first verification command (e.g. `#check_invariants`) generates the definitions and runs the checks. \
  If the option is turned off within a module, the next declaration or `#gen_spec` first generates the definitions deferred so far. \
  `#model_check`, `#simulate`, and `#liveness_check` need neither."
}

register_option veil.simulate.numTraces : Nat := {
  defValue := 10000
  descr := "Number of simulation traces to attempt, stopping early on a violation or cancellation. Default is 10000."
}

register_option veil.simulate.maxSteps : Nat := {
  defValue := 100
  descr := "Maximum number of action transitions per simulation trace, excluding the initial state. Default is 100."
}

register_option veil.modelChecker.emitTimings : Bool := {
  defValue := false
  descr := "If true, `#model_check`, `#simulate` and `#liveness_check` each write one compact JSON \
  object to the *Lean process's* stderr when a run finishes, under the key `veil_timing`. It carries \
  the command, the execution mode, the wall clock of the run as the progress widget measured it, the \
  compilation wall clock when a binary was built, and the runner's own `timing` object when it reports \
  one (`#liveness_check` reports the route and the per-property search time). Intended for benchmark \
  harnesses: a compiled run's numbers are produced inside the worker process, whose stdout and stderr \
  the elaborator consumes, so this is the only place they can be read from outside. Off by default, \
  since the infoview already shows all of it."
}

register_option veil.modelChecker.maxStoredBuilds : Nat := {
  defValue := 1
  descr := "Maximum number of compiled builds of `#model_check`, `#simulate`, and `#liveness_check` stored in \
  `.lake/model_checker_builds`; 0 means no limit, so builds are never deleted. When a run ends, \
  cleanup keeps the most recently compiled builds up to this limit, allowing later runs to reuse \
  them. Builds that running checks use are never deleted, even beyond the limit. Cleanup is \
  skipped if another build holds the build lock. The default of 1 retains the latest build."
}

register_option veil.modelChecker.buildOnly : Bool := {
  defValue := false
  descr := "If true, a `compiled` `#model_check`, `#simulate` or `#liveness_check` builds its \
  worker binary and stops, without running it. The build folder is reported on the Lean process's \
  stderr under the key `veil_build` when `veil.modelChecker.emitTimings` is also set. Intended for \
  a benchmark harness that wants the build out of the measurement entirely: it elaborates and \
  builds every case in one pass, then runs each binary itself, so that no elaboration, code \
  generation or Lake invocation is ever inside a measured interval or a timeout. Combine with \
  `--property` on the binary to measure one property at a time from a single build. Has no effect \
  on `interpreted` runs, which compile nothing. Off by default."
}

end Veil
