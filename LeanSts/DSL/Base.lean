import Lean
open Lean

register_simp_attr invSimp
register_simp_attr actSimp
register_simp_attr initSimp
register_simp_attr safeSimp

initialize
  registerTraceClass `dsl
  registerTraceClass `dsl.debug
  -- the following are primarily for performance profiling
  registerTraceClass `dsl.perf.checkInvariants
