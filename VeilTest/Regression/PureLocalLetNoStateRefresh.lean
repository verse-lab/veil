import Veil

set_option linter.unusedTactic false

open Lean Elab Tactic Meta in
elab "log_lctx_size" : tactic => do
  let lctx ← getLCtx
  -- Lean 4.32 introduces inaccessible implementation-detail locals named `__r`
  -- while elaborating the generated state accessors.  They are not source-level
  -- declarations and should not affect this regression test's context-size metric.
  let declarations := lctx.getFVarIds.filter fun id =>
    (lctx.get! id).userName.getRoot != `__r
  logInfo m!"local declarations: {declarations.size}"

/-!
# Regression: pure local lets do not refresh state binders

Ordinary local `let` statements do not mutate Veil state, so they should not
trigger the state-binder refresh machinery. Otherwise every pure local binding
reintroduces all mutable fields into the local context. The `#guard_msgs`
below pins the local-context size observed inside the last pure `let`.
-/

veil module PureLocalLetNoStateRefresh

type t
relation r1 : t → t → Bool
relation r2 : t → t → Bool
relation r3 : t → t → Bool

#gen_state

/-- info: local declarations: 21
---
info: local declarations: 22
---
info: local declarations: 23
---
info: local declarations: 24
-/
#guard_msgs(info, drop warning) in
action pure_local_lets {
  let z1 := (by
    log_lctx_size
    exact 0)
  let mut z2 := (by
    log_lctx_size
    exact 0)
  let z3 := (by
    log_lctx_size
    exact 0)
  let mut z4 := (by
    log_lctx_size
    exact 0)
  require z1 + z2 > z3 + z4
}

end PureLocalLetNoStateRefresh
