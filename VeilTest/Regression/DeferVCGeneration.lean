module

public import Veil

/-! # `veil.deferVCGeneration`

Procedures declared with this option do not generate their WP-based
verification definitions, and `#gen_spec` generates no verification conditions,
so it also skips the `doesNotThrow` checks. The first verification command
generates the definitions as the declarations would have, then does what
`#gen_spec` skipped. -/

open Lean in
/-- Check that modules `lhs` and `rhs`, which have the same content, got the
same verification definitions up to the module prefix. -/
private meta def checkSameVerificationDefinitions (lhs rhs : Name) (procs : List Name) :
    MetaM Unit := withoutExporting do
  let env ← getEnv
  let rn (n : Name) := if lhs.isPrefixOf n then n.replacePrefix lhs rhs else n
  -- Module names occur in constants and in primitive projections.
  let rename (e : Expr) : MetaM Expr := Core.transform e (post := fun
    | .const n us => return .done (.const (rn n) us)
    | .proj s i x => return .done (.proj (rn s) i x)
    | e => return .done e)
  let mut compared := 0
  for p in procs do
    for sfx in [`wp, `wp_eq, `ext.wp, `ext.wp_eq, `ext.tr, `ext.tr_eq_wpSucc, `ext.derived_eq,
        `ext.wp_local_eq, `ext.wp_local_eq.pred, `ext.wp_eq.local, `ext.tr_abstract] do
      let (l, r) := (lhs ++ p ++ sfx, rhs ++ p ++ sfx)
      match env.find? l, env.find? r with
      | none, none => pure ()
      | some cl, some cr =>
        unless (← rename cl.type) == cr.type do throwError "the type of {r} differs from {l}"
        if let (.defnInfo dl, .defnInfo dr) := (cl, cr) then
          unless (← rename dl.value) == dr.value do throwError "the value of {r} differs from {l}"
        compared := compared + 1
      | _, _ => throwError "{l} and {r} are not both defined"
  if compared == 0 then throwError "no verification definitions to compare"

veil module DeferWP
set_option veil.deferVCGeneration true
individual flag : Bool
after_init { flag := false }
procedure assign_flag (b : Bool) { flag := b }
action toggle { assign_flag (!flag) }
invariant [flag_bool] flag = true ∨ flag = false
#gen_spec

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

-- Neither `#gen_spec` nor model checking needs the WPs.
run_cmd do
  let env ← Lean.getEnv
  for n in [`DeferWP.initializer.wp, `DeferWP.assign_flag.wp, `DeferWP.toggle.wp,
      `DeferWP.toggle.ext.wp, `DeferWP.toggle.ext.tr, `DeferWP.relationalTransitionSystem] do
    if env.contains n then throwError "generated before a verification command: {n}"

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  flag_bool ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  toggle
    doesNotThrow ... ✅
    flag_bool ... ✅
-/
#guard_msgs in
#check_invariants

run_cmd do
  let env ← Lean.getEnv
  for n in [`DeferWP.initializer.wp, `DeferWP.assign_flag.wp, `DeferWP.toggle.wp,
      `DeferWP.toggle.ext.wp, `DeferWP.toggle.ext.tr, `DeferWP.relationalTransitionSystem] do
    unless env.contains n do throwError "missing after #check_invariants: {n}"

-- Later verification commands reuse what the first one generated.
#check_action toggle
#gen_theorems
end DeferWP

veil module DeferAssert
set_option veil.deferVCGeneration true
individual active : Bool
#gen_state
after_init { active := false }
action fail { assert false }
invariant true

-- The assertion check waits for a verification command ...
#guard_msgs in
#gen_spec

-- ... while model checking still finds reachable assertion failures.
/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    active = false
  State 1 (via fail):
    active = false
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

set_option veil.printCounterexamples false in
/--
error: This assertion might fail when called from fail
---
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  fail
    doesNotThrow ... ❌
    inv_0 ... ✅
-/
#guard_msgs in
#check_invariants
end DeferAssert

-- A `#gen_spec` run without the option generates the deferred definitions and
-- checks assertions as usual.
veil module DeferThenCheck
set_option veil.deferVCGeneration true
individual active : Bool
#gen_state
after_init { active := false }
action fail { assert false }
invariant true
set_option veil.deferVCGeneration false

/-- error: This assertion might fail when called from fail -/
#guard_msgs in
#gen_spec
end DeferThenCheck

-- Deferred definitions are generated under the options of their declaration.
veil module DeferOptions
set_option veil.deferVCGeneration true
type node
immutable function val : node → Nat
individual x : Nat
after_init { x := 0 }
set_option veil.experimental.wpCompact false
action compact_off (n : node) {
  if (val n) > 10 then x := (val n) else x := (val n) + 1
}
set_option veil.experimental.wpCompact true
action compact_on (n : node) {
  if (val n) > 10 then x := (val n) else x := (val n) + 1
}
invariant True
#gen_spec
#check_invariants

run_meta Lean.withoutExporting do
  let env ← Lean.getEnv
  for (n, expected) in [(`DeferOptions.compact_off.ext.wp_local_eq.pred, false),
      (`DeferOptions.compact_on.ext.wp_local_eq.pred, true)] do
    let some decl := env.find? n | throwError "missing predicate: {n}"
    let hasLetEq := (decl.value!.find? (·.isConstOf ``Veil.letEq)).isSome
    unless hasLetEq == expected do throwError "declaration-time options not used for {n}"
end DeferOptions

-- The same specification three times: eager, deferred, and deferred procedures
-- followed by eager actions (which generate the deferred ones first).
veil module EagerSame
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
procedure p2 (n : node) { p1 true; cnt := cnt + val n; seen n := true }
action a (n : node) { p2 n; p1 false }
action b2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p2 n else cnt := val m
}
action c3 (n : node) { assert cnt ≥ 0; seen N := N = n }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
#gen_spec
#check_invariants
end EagerSame

veil module DeferredSame
set_option veil.deferVCGeneration true
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
procedure p2 (n : node) { p1 true; cnt := cnt + val n; seen n := true }
action a (n : node) { p2 n; p1 false }
action b2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p2 n else cnt := val m
}
action c3 (n : node) { assert cnt ≥ 0; seen N := N = n }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
#gen_spec
#check_invariants
end DeferredSame

veil module MixedSame
set_option veil.deferVCGeneration true
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
procedure p2 (n : node) { p1 true; cnt := cnt + val n; seen n := true }
set_option veil.deferVCGeneration false
action a (n : node) { p2 n; p1 false }
action b2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p2 n else cnt := val m
}
action c3 (n : node) { assert cnt ≥ 0; seen N := N = n }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
#gen_spec
#check_invariants
end MixedSame

run_meta do
  let procs := [`initializer, `p1, `p2, `a, `b2, `c3]
  checkSameVerificationDefinitions `EagerSame `DeferredSame procs
  checkSameVerificationDefinitions `EagerSame `MixedSame procs

/-! ## Toggling the option repeatedly

`ToggledA` and `ToggledB` switch `veil.deferVCGeneration` on and off many times,
with calls across the switches, a ghost definition between them, a
`set_option … in`, a per-action `wpCompact`, and a transition-form action.
Both must end up with the same verification definitions as `ToggledEager`. -/

veil module ToggledEager
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
procedure p2 (n : node) { p1 true; cnt := cnt + val n }
action a1 (n : node) { p2 n; seen n := true }
ghost relation seenSome := if (∃ N, seen N) then true else false
procedure p3 (n : node) { p1 false; p2 n }
action a2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p3 n else cnt := val m
}
set_option veil.experimental.wpCompact false
action a3 (n : node) { assert cnt ≥ 0; p3 n }
set_option veil.experimental.wpCompact true
action a4 (n : node) { p1 true; seen n := false }
transition bump (n : node) {
  cnt' = cnt + val n ∧ flag' = flag ∧ (∀ N, seen' N = seen N)
}
action a5 (n : node) { p3 n; p1 true }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
#gen_spec
#check_invariants
end ToggledEager

veil module ToggledA
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
set_option veil.deferVCGeneration true
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
set_option veil.deferVCGeneration false
procedure p2 (n : node) { p1 true; cnt := cnt + val n }
set_option veil.deferVCGeneration true
action a1 (n : node) { p2 n; seen n := true }
ghost relation seenSome := if (∃ N, seen N) then true else false
procedure p3 (n : node) { p1 false; p2 n }
set_option veil.deferVCGeneration false
set_option veil.deferVCGeneration true
set_option veil.deferVCGeneration false
action a2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p3 n else cnt := val m
}
set_option veil.deferVCGeneration true
set_option veil.experimental.wpCompact false
action a3 (n : node) { assert cnt ≥ 0; p3 n }
set_option veil.experimental.wpCompact true
set_option veil.deferVCGeneration false in
action a4 (n : node) { p1 true; seen n := false }
transition bump (n : node) {
  cnt' = cnt + val n ∧ flag' = flag ∧ (∀ N, seen' N = seen N)
}
action a5 (n : node) { p3 n; p1 true }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
#gen_spec

-- Each eager declaration generated what was deferred before it; only the
-- declarations after the last one (`a4`) still wait.
run_cmd do
  let env ← Lean.getEnv
  for n in [`ToggledA.initializer.ext.wp, `ToggledA.p1.wp, `ToggledA.p2.wp, `ToggledA.a1.ext.wp, `ToggledA.p3.wp, `ToggledA.a2.ext.wp, `ToggledA.a3.ext.wp, `ToggledA.a4.ext.wp] do
    unless env.contains n do throwError "not generated by an eager declaration: {n}"
  for n in [`ToggledA.bump.ext.wp, `ToggledA.a5.ext.wp, `ToggledA.relationalTransitionSystem] do
    if env.contains n then throwError "generated before a verification command: {n}"

#check_invariants
end ToggledA

-- Set outside the module: it stays set after `end`, unlike the settings inside.
set_option veil.deferVCGeneration true

veil module ToggledB
type node
immutable function val : node → Nat
individual flag : Bool
individual cnt : Nat
relation seen : node → Bool
set_option veil.deferVCGeneration true
after_init { flag := false; cnt := 0; seen N := false }
procedure p1 (b : Bool) { flag := b }
set_option veil.deferVCGeneration false
procedure p2 (n : node) { p1 true; cnt := cnt + val n }
set_option veil.deferVCGeneration true
action a1 (n : node) { p2 n; seen n := true }
ghost relation seenSome := if (∃ N, seen N) then true else false
procedure p3 (n : node) { p1 false; p2 n }
set_option veil.deferVCGeneration false
set_option veil.deferVCGeneration true
set_option veil.deferVCGeneration false
action a2 (n : node) (m : node) {
  require val m > 0
  if val m > 3 then p3 n else cnt := val m
}
set_option veil.deferVCGeneration true
set_option veil.experimental.wpCompact false
action a3 (n : node) { assert cnt ≥ 0; p3 n }
set_option veil.experimental.wpCompact true
set_option veil.deferVCGeneration false in
action a4 (n : node) { p1 true; seen n := false }
transition bump (n : node) {
  cnt' = cnt + val n ∧ flag' = flag ∧ (∀ N, seen' N = seen N)
}
action a5 (n : node) { p3 n; p1 true }
invariant [flag_bool] flag = true ∨ flag = false
invariant [cnt_nonneg] cnt ≥ 0
set_option veil.deferVCGeneration false
#gen_spec
#check_invariants
end ToggledB

set_option veil.deferVCGeneration false

run_meta do
  let procs := [`initializer, `p1, `p2, `a1, `p3, `a2, `a3, `a4, `bump, `a5]
  checkSameVerificationDefinitions `ToggledEager `ToggledA procs
  checkSameVerificationDefinitions `ToggledEager `ToggledB procs
