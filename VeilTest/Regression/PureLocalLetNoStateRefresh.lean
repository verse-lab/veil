import Veil

set_option linter.unusedTactic false

open Lean Elab Tactic Meta in
elab "log_lctx_size" : tactic => do
  let lctx ← getLCtx
  -- Lean 4.32 introduces inaccessible implementation-detail locals named `__r`
  -- while elaborating generated state accessors. Veil's extensible-do port also
  -- opens a fresh implementation-detail state view before every statement.
  -- Neither is source-level and neither should affect this metric.
  let declarations := lctx.getFVarIds.filter fun id =>
    let decl := lctx.get! id
    decl.kind != .implDetail &&
      decl.userName.getRoot != `__r &&
      !Veil.isVeilImplementationDetailName decl.userName
  logInfo m!"local declarations: {declarations.size}"

/-!
# Regression: per-statement state views do not leak into user scope

Every statement receives a fresh current-state view, including ordinary local
`let` statements. Those generated declarations are implementation details, so
the user-visible context below must still grow only with the source-level local
bindings.
-/

veil module PureLocalLetNoStateRefresh

type t
relation r1 : t → t → Bool
relation r2 : t → t → Bool
relation r3 : t → t → Bool

#gen_state

/-- info: local declarations: 10
---
info: local declarations: 11
---
info: local declarations: 12
---
info: local declarations: 13
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
