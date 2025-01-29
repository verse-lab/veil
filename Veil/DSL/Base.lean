import Lean
open Lean

register_simp_attr invSimp
register_simp_attr ifSimp
register_simp_attr actSimp
register_simp_attr wlpSimp
register_simp_attr initSimp
register_simp_attr safeSimp
register_simp_attr genSimp

initialize
  registerTraceClass `dsl
  registerTraceClass `dsl.debug
  registerTraceClass `dsl.info
  -- the following are primarily for performance profiling
  registerTraceClass `dsl.perf.checkInvariants

register_option veil.gen_sound : Bool := {
  defValue := false
  descr := "generate soundness instances for actions"
}
