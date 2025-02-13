import Lean
import Veil.SMT.Base
import Auto.Solver.SMT

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
  registerTraceClass `veil
  registerTraceClass `veil.info
  registerTraceClass `veil.warning
  registerTraceClass `veil.debug

  registerTraceClass `veil.smt
  registerTraceClass `veil.smt.query
  registerTraceClass `veil.smt.result
  registerTraceClass `veil.smt.model
  registerTraceClass `veil.smt.debug

  -- the following are primarily for performance profiling
  registerTraceClass `veil.smt.perf.translate
  registerTraceClass `veil.smt.perf.query
  registerTraceClass `veil.smt.perf.checkSat
  registerTraceClass `veil.smt.perf.getModel
  registerTraceClass `veil.smt.perf.minimizeModel

/-! ## Options -/

register_option veil.gen_sound : Bool := {
  defValue := false
  descr := "Generate soundness instances for actions."
}

register_option veil.printCounterexamples : Bool := {
  defValue := false
  descr := "Print counterexamples (models) when they are found in `#check_invariants`."
}

open Auto.Solver.SMT in
register_option veil.smt.solver : SolverName := {
  defValue := SolverName.z3
  descr := "SMT solver to use"
}

register_option veil.smt.seed : Nat := {
  defValue := 0xcafe
  descr := "SMT seed to use"
}

register_option veil.smt.model.minimize : Bool := {
  defValue := false
  descr := "Should models be minimized before being displayed?"
}

register_option veil.smt.translator : SmtTranslator := {
  defValue := SmtTranslator.leanAuto
  descr := "Which package to use for translating Lean to SMT (`lean-auto` or `lean-smt`)"
}

register_option veil.smt.reconstructProofs : Bool := {
  defValue := false
  descr := "Whether to use Lean SMT's proof reconstruction"
}

register_option veil.smt.macrofinder : Bool := {
  defValue := false
  descr := "Whether to use Z3's macro-finder tactic"
}

/-! ## `simp` attributes

We have a large number of `simp` attributes in Veil, since we want
precise control over what gets simplified when. Moreover, we want to
keep simplification times low, so we purposefully keep our lemma sets
small.

We use these attributes to control simplification in our DSL constructs
(e.g. `action`) and in the verification conditions (VCs) we generate.
-/

/-! ### General -/

/-- Simplifiers to prepare a goal for SMT. See `SMT/Preparation.lean`.
This is designed to be a "cheap" lemma set, that can be quickly
applied. -/
register_simp_attr smtSimp

/-- Simplifiers to get rid of trivial if conditions. We need these to
simplify `Wlp` goals. -/
register_simp_attr ifSimp

/-- We specifically identify lemmas for quantifier elimination and
hoisting, since we run these in a loop and `logicSimp` is too
large/expensive a set to run in a loop. See `SMT/Preparation.lean` -/
register_simp_attr quantifierSimp

/-- Simplifiers to perform logic-based simplification. This mostly
corresponds to Lean's default `simp` set, but with some lemmas that
change quantifier structure removed. (We remove these lemmas because we
need to be careful to preserve decidability of our queries, and
changing the quantifier structure is a sure-fire way of losing
decidability, even if the obtained goals are logically equivalent.) -/
register_simp_attr logicSimp


/-! ### DSL-specific -/

/-- Attribute added to conjunctions of invariant clauses, to unfold
them into their components named invariants. -/
register_simp_attr invSimpTopLevel

/-- Attribute added to invariant clauses, as well as conjunctions of
invariant clauses, to unfold them. -/
register_simp_attr invSimp

/-- Attribute added to individual safety clauses, as well as the
top-level safety property. -/
register_simp_attr safeSimp

/-- Attribute added to initial state specifications. -/
register_simp_attr initSimp

/-- Attribute added to individual actions, as well as collections of
actions, to unfold them. -/
register_simp_attr actSimp

/-- Attribute added to `Wlp` constructs, to unfold them. -/
register_simp_attr wlpSimp
