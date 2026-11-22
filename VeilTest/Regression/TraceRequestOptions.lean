module

public import Veil
public meta import Smt

/-! Real trace requests for the incremental LSP test. The probe observes the
configuration passed to the ordinary SMT tactic. With no test driver attached
the queries run directly, as they do during `lake test`. -/

-- The LSP driver supplies its temporary worker log in the virtual document.
private meta def workerLog : Option System.FilePath := none

open Lean Elab Tactic Parser.Tactic Smt.Tactic in
@[local tactic Smt.Tactic.smt]
meta def observeTraceSolver : Tactic := fun stx => do
  if let some log := workerLog then
    let `(tactic| smt $opts:optConfig $_:smtHints) := stx | throwUnsupportedSyntax
    let cfg ← elabConfig opts
    let timeout := cfg.timeout.getD 0
    IO.FS.withFile log .append fun h => h.putStrLn s!"{timeout}"
    -- A bounded gate allows the driver to edit a query while its worker runs.
    let gate := log.withExtension s!"block-{timeout}"
    if ← gate.pathExists then
      for _ in [:1500] do
        unless ← gate.pathExists do break
        IO.sleep 20
      if ← gate.pathExists then throwError "Trace request test gate timed out"
      try evalSmt stx
      finally IO.FS.withFile log .append fun h => h.putStrLn s!"finished-{timeout}"
      return
  evalSmt stx

-- Source-level trace commands generate fresh binder syntax. Selecting the
-- already registered VC also tests a retry of exactly the same graph node.
private meta def retryExistingTrace (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let result ← Veil.Verifier.waitFilteredSync fun
    | .trace metadata => metadata.traceName == some name
    | _ => false
  unless result.vcs.size == 1 && result.vcs.all (·.status == some .proven) do
    throwError "expected a single successful trace check for {name}"

veil module TraceRequestOptions

individual flag : Bool
after_init { flag := false }
action setFlag { flag := true }
invariant flag = false ∨ flag = true
#gen_spec

section
set_option veil.smt.timeout 71 in
sat trace [reachable] {
  setFlag
  assert flag
}
end

section
set_option veil.smt.timeout 72 in
unsat trace [initialTrue] { assert flag }
end

end TraceRequestOptions
