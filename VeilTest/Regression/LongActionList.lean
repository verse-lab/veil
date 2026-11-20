module

public import Veil

/-! Generating and narrowing `Next.tr_abstract` with a list long enough for
Lean to elaborate it in `let`-bound chunks. -/

veil module LongActionList

individual flag : Bool

after_init { flag := false }

action a1 { flag := !flag }
action a2 { flag := !flag }
action a3 { flag := !flag }
action a4 { flag := !flag }
action a5 { flag := !flag }
action a6 { flag := !flag }
action a7 { flag := !flag }
action a8 { flag := !flag }
action a9 { flag := !flag }
action a10 { flag := !flag }
action a11 { flag := !flag }
action a12 { flag := !flag }
action a13 { flag := !flag }
action a14 { flag := !flag }
action a15 { flag := !flag }
action a16 { flag := !flag }
action a17 { flag := !flag }
action a18 { flag := !flag }
action a19 { flag := !flag }
action a20 { flag := !flag }
action a21 { flag := !flag }
action a22 { flag := !flag }
action a23 { flag := !flag }
action a24 { flag := !flag }
action a25 { flag := !flag }
action a26 { flag := !flag }
action a27 { flag := !flag }
action a28 { flag := !flag }
action a29 { flag := !flag }
action a30 { flag := !flag }
action a31 { flag := !flag }
action a32 { flag := !flag }
action a33 { flag := !flag }
action a34 { flag := !flag }
action a35 { flag := !flag }

invariant flag ∨ ¬ flag

#guard_msgs in
#gen_spec

-- With no excluded actions, narrowing must pass all 35 indices to `Next.tr_abstract`.
example (th : ρ) (s₀ s₁ : σ) (h : (veil_term% NextStep) s₀ s₁) : True := by
  __liveness_narrow_action
  guard_hyp h :~ _ ∨ _
  trivial

end LongActionList
