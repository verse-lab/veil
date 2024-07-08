import LeanSts.Tactic

set_option trace.smt true
set_option trace.smt.solve true


theorem extracted {round : Type} [round_dec : DecidableEq round]
  (st_one_a : round → Prop) (st'_one_a : round → Prop)
  (hnext : ∃ r, (∀ (x : round), st'_one_a x = if x = r then True else st_one_a x))
  : True := by
  smt [hnext]

namespace Uninterpreted
variable {T : Type} [Nonempty T] (le : T → T → Prop)

axiom refl    : ∀ x, le x x
axiom trans   : ∀ x y z, le x y → le y z → le x z
axiom antisym : ∀ x y, le x y → le y x → x = y
axiom total   : ∀ x y, le x y ∨ le y x

theorem x : ∀ x, le x x := by
  smt [refl le]

end Uninterpreted

section UninterpretedWithClass
class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Prop
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

variable {t : Type} [ne : Nonempty t]
example [tot : TotalOrder t] : ∀ (x : t), tot.le x x := by
  rcases tot with ⟨le, le_refl, le_trans, le_antisymm, le_total⟩
  simp only [TotalOrder.le] -- this is strictly needed!
  smt [le_refl]

end UninterpretedWithClass
