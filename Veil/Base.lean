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

register_option veil.experimental.generateWpLocalEq : Bool := {
  defValue := true
  descr := "Experimental. If true, `wp_local_eq` theorems will be generated after `wp` generation."
}

register_option veil.experimental.wpCompact : Bool := {
  defValue := true
  descr := "Experimental. If true, compact generated `wp_local_eq.pred` definitions by sharing duplicated postcondition branches with `letEq` and exposing abstract-state conditionals field-wise."
}

end Veil
