import Veil.Frontend.DSL.Tactic.Core
import Smt

open Lean Elab Tactic Meta Simp Tactic.TryThis Parser.Tactic
namespace Veil

private def mkVeilSmtTactic : TacticM (TSyntax `tactic) := do
  let idents ← getPropsInContext
  let opts ← getOptions
  let fmfEnabled := veil.smt.finiteModelFind.get opts
  let timeout := veil.smt.timeout.get opts
  let trustEnabled := veil.smt.trust.get opts
  let fmfValue := if fmfEnabled then "true" else "false"
  let trustSmt := mkIdent <| if trustEnabled then ``true else ``false
  let embedBool := mkIdent <| if trustEnabled then ``false else ``true
  let solverOptions ← `(term| [("finite-model-find", $(Syntax.mkStrLit fmfValue)), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let smtTac ← `(tactic|
    open $(mkIdent `Classical):ident in
    smt
      ($(mkIdent `trust):ident := $trustSmt:ident)
      ($(mkIdent `embedBool):ident := $embedBool:ident)
      ($(mkIdent `model):ident := $(mkIdent ``true))
      ($(mkIdent `timeout):ident := $(mkIdent ``Option.some) $(quote timeout))
      ($(mkIdent `extraSolverOptions):ident := $solverOptions)
      [$[$idents:ident],*])
  if trustEnabled then
    return smtTac
  else
    return ← `(tactic| (veil_infer_nonempty; $smtTac:tactic))

def elabVeilSmt (stx : Syntax) (trace : Bool := false) : DesugarTacticM Unit := withBackwardsCompatibility <| veilWithMainContext do
  -- It's necessary to `open Classical` to make proof reconstruction work.
  -- Otherwise, sometimes it fails due to failing to infer `Decidable` instances.
  let auto_tac ← mkVeilSmtTactic
  if trace then
    addSuggestion stx auto_tac
  else
    veilEvalTactic auto_tac

@[tactic veil_smt, tactic veil_smt_trace]
def elabVeilSmtTactics : Tactic := fun stx => do
  let res : DesugarTacticM Unit :=
  match stx with
  | `(tactic| veil_smt%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt") $ elabVeilSmt tk
  | `(tactic| veil_smt?%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt?") $ elabVeilSmt tk true
  | _ => throwUnsupportedSyntax
  res.runByOption stx

end Veil
