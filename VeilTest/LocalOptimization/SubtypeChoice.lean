module

public import Veil

veil module LocalSubtypeChoice

individual x : Nat

#gen_state

after_init { x := 0 }

-- The selected type depends on the state after the update. Its WP originally
-- retained getFrom (setIn ... s) inside the Subtype domain, blocking wp_local_eq.
#guard_msgs in
action chooseBounded {
  x := x + 1
  let bound := x
  let n : {n : Nat // n ≤ bound} :| n.val ≤ bound
  x := n.val
}

invariant [nonnegative] 0 ≤ x

#guard_msgs in
#gen_spec

-- Ensure local WP/TR artifacts exist: conservative fallback is not success.
run_cmd do
  discard <| Lean.getConstInfo ``chooseBounded.ext.wp_local_eq
  discard <| Lean.getConstInfo ``chooseBounded.ext.tr_abstract
  discard <| Lean.getConstInfo ``Next.tr_abstract

end LocalSubtypeChoice
