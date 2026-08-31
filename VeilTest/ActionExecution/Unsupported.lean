import Veil

/-! Diagnostics for every control/effect construct excluded from Veil actions. -/

set_option linter.unusedVariables false

veil module ActionExecutionUnsupported

individual x : Bool

#gen_state

/-- error: Error in action reject_while: `while` loops are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_while {
  while x do
    x := false
}

/-- error: Error in action reject_repeat: `repeat` loops are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_repeat {
  repeat
    x := false
}

/-- error: Error in action reject_repeat_until: `repeat` loops are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_repeat_until {
  repeat
    x := false
  until x
}

/-- error: Error in action reject_try: exceptions (`try`/`catch`/`finally`) are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_try {
  try
    x := true
  catch _ =>
    x := false
}

/-- error: Error in action reject_break: `break` is not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_break {
  break
}

/-- error: Error in action reject_continue: `continue` is not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_continue {
  continue
}

/-- error: Error in action reject_let_rec: recursive local declarations are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_let_rec {
  let rec loop (n : Nat) : Nat := loop n
  let _ := loop 0
}

/-- error: Error in action reject_forward: effect forwarding (`do←`) is not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_forward {
  id (do←
    x := true)
}

/-- error: Error in action reject_match_expr: `match_expr` is not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_match_expr {
  match_expr x with
  | true => x := false
  | _ => pure ()
}

/-- error: Error in action reject_assert_bang: Lean `assert!` is not supported in Veil actions; use Veil `assert` -/
#guard_msgs(error, drop warning) in
action reject_assert_bang {
  assert! x
}

/-- error: Error in action reject_debug_assert: Lean `debug_assert!` is not supported in Veil actions; use Veil `assert` -/
#guard_msgs(error, drop warning) in
action reject_debug_assert {
  debug_assert! x
}

end ActionExecutionUnsupported
