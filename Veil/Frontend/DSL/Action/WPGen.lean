import Lean
import Veil.Frontend.DSL.Action.Semantics.WP
import Veil.Util.Meta
import Veil.Frontend.DSL.Infra.Simp

namespace Veil

open Lean Meta Elab

attribute [substateSimp ↓] IsSubStateOf.setIn_getFrom_idempotent IsSubStateOf.setIn_setIn_last IsSubStateOf.getFrom_setIn_idempotent

simproc_decl wpGenEqOnly (wp _ _) := fun e => do
  -- Imagine that there are two sets of theorems related to the term starting with `wp`:
  -- (1) theorems for `wp` of atoms (e.g., for `get` there is `VeilM.wp_get`) and
  -- (2) theorems for `wp` of the declarations which have been generated (e.g., for `wp foo` there is `foo.wp_eq`)
  -- An experience is the (2) theorems will be used __only__ when actions are not eagerly unfolded,
  -- say, not marked as `reducible`.
  trace[veil.wp] "when simp in wpGenEqOnly : {e}"
  let .some a ← getSimpExtension? `wpSimp | return .continue
  let b ← SimpExtension.getTheorems a
  withTheReader Simp.Context (fun ctx => ctx.setSimpTheorems (ctx.simpTheorems.push b)) do
  let .some a ← getSimpExtension? `wpEqSimp | return .continue
  let b ← SimpExtension.getTheorems a
  withTheReader Simp.Context (fun ctx => ctx.setSimpTheorems (ctx.simpTheorems.push b)) do
    -- `Simp.rewritePre` will do the rewriting using `pre` theorems
    Simp.rewritePre false e

def wpGenBySimprocCore (e : Expr) : TermElabM (Expr × Expr) := do
  -- The following code prepares a minimal simp context.
  let simprocs ← do
    let tmp : Simp.SimprocsArray := #[]
    let tmp ← tmp.add ``wpGenEqOnly false
    pure tmp
  -- After rewriting using various `wp_eq` theorems, we might end up with
  -- `foo.wpGen`, `bar.wpGen`, etc. To unfold them, we can either declare them as
  -- `reducible`, or register them to be unfolded, as using `wpDefUnfoldSimp` here.
  let ctx ← Simp.mkVeilSimpCtx #[`substateSimp, `wpDefUnfoldSimp]
  -- Some definitions like `foo.wpGen` will be only partially applied
  -- __after doing WP generation and before further simplification__,
  -- so need to enable this option to unfold them; otherwise the unfold lemmas will __not__ be used.
  -- This _might_ be dealt in a different way (e.g., by controlling the type of `wpGen`
  -- to "disallow" certain eta-expansions; more specifically, make the return type
  -- be `SProp` rather than `ρ → σ → Prop`).
  let ctx ← ctx.setConfig { ctx.config with unfoldPartialApp := true }
  let (res, _stats) ← Meta.simp e ctx (simprocs := simprocs) (discharge? := none)
  return (res.expr, ← res.getProof)

end Veil
