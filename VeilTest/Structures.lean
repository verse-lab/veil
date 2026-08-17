import Veil

set_option veil.smt.trust false

namespace StructureSupportTypes

@[veil_decl]
structure StructurePoint where
  x : Int
  enabled : Bool

@[veil_decl]
structure StructureEnvelope where
  point : StructurePoint
  sequence : Int

end StructureSupportTypes

open StructureSupportTypes

veil module StructureSupport

individual point : StructurePoint
individual envelope : StructureEnvelope
individual pair : Int × Bool
individual triplet : Int × Bool × Bool

after_init {
  point := { x := 0, enabled := false }
  envelope := { point := { x := 2, enabled := true }, sequence := 3 }
  pair := (4, true)
  triplet := (5, true, false)
}

action change {
  point := { x := 7, enabled := true }
  pair := (8, false)
  triplet := (42, false, true)
}

invariant point.x ≥ 0
invariant envelope.point.x = 2
invariant pair.1 ≥ 0

#gen_spec

#guard_msgs(drop info) in
#check_invariants

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    envelope = {point: {enabled: true, x: 2}, sequence: 3}
    pair = [4, true]
    point = {enabled: false, x: 0}
    triplet = [5, [true, false]]
  State 1 (via change):
    envelope = {point: {enabled: true, x: 2}, sequence: 3}
    pair = [8, false]
    point = {enabled: true, x: 7}
    triplet = [42, [false, true]]
-/
#guard_msgs in
sat trace { change }

#guard_msgs in
unsat trace {
  change
  assert (pair.1 = 4)
}

end StructureSupport

namespace StructureTagDiagnostic

structure Untagged where
  value : Int

/--
error: Structure StructureTagDiagnostic.Untagged is used in an SMT obligation but is not marked with `@[veil_decl]`
-/
#guard_msgs in
example (item : Untagged) : True := by
  veil_fol

end StructureTagDiagnostic

example (left right : Int × Bool)
    (fst_eq : left.1 = right.1) (snd_eq : left.2 = right.2) : left = right := by
  veil_fol
  veil_smt
