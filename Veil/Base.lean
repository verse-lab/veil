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

register_option veil.violationIsError : Bool := {
  defValue := true
  descr := "If true, violations found by verification or model checking are \
  logged as errors. If false, they are logged as info messages."
}

register_option veil.__modelCheckCompileMode : Bool := {
  defValue := false
  descr := "(INTERNAL ONLY. DO NOT USE.) When true, skip verification-only operations for model checking compilation."
}

end Veil
