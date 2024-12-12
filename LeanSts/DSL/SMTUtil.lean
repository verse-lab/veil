import Smt
import Lean
import LeanSts.SMT.Main
import Auto.Solver.SMT

open Smt Smt.Tactic Translate Lean Lean.Meta Auto.Solver.SMT in
def querySolverWithIndicators (goalQuery : String) (timeout : Nat) (checks: Array ((Name × Expr) × (Name × Expr))) (forceSolver : Option SolverName := none)
  (retryOnFailure : Bool := false) (getModel? : Bool := true) (minimize : Option Bool := none) : MetaM (List (Name × Name × SmtResult)) := do
  withTraceNode `sauto.perf.query (fun _ => return "querySolver") do
  let opts ← getOptions
    let minimize := minimize.getD (sauto.model.minimize.get opts)
    let solverName :=
      match forceSolver with
      | some s => s
      | none => sauto.smt.solver.get opts
    trace[sauto.debug] "solver: {solverName}"
  try
    let solver ← createSolver solverName timeout
    if solverName == SolverName.cvc5 then
      emitCommand solver (.setLogic "ALL")
      emitCommand solver (.setOption (.produceProofs true))
      emitCommand solver (.setOption (.produceUnsatCores true))
    emitCommandStr solver goalQuery
    let mut ret := []
    for ((act, actInd), (inv, invInd)) in checks do
      emitCommandStr solver "(push)"
      emitCommandStr solver s!"(assert {actInd})"
      emitCommandStr solver s!"(assert {invInd})"
      let result ← getSolverResult solver solverName minimize false (if retryOnFailure then 1 else 0)
      ret := ret ++ [((act, inv, result))]
      emitCommandStr solver "(pop)"
    solver.kill
    return ret
  catch e =>
    let exMsg ← e.toMessageData.toString
    let mut ret := []
    for ((act, actInd), (inv, invInd)) in checks do
      ret := ret ++ [(act, inv, .Unknown s!"{exMsg}")]
    return ret

where getSolverResult (solver: SolverProc) (solverName: SolverName) (minimize: Bool) (kill: Bool) (retries: Nat) : MetaM SmtResult := do
  -- TODO: querySolver should use this version of the function.
  let checkSatResponse ← checkSat solver solverName
    match checkSatResponse with
    | .Sat =>
        trace[sauto.result] "{solverName} says Sat"
        if getModel? then
          let model ← getModel solver
          trace[sauto.debug] "Model:\n{model}"
          -- For Z3, we have model pretty-printing and minimization.
          if solverName == SolverName.z3 then
            let mut fostruct ← extractStructure model
            if minimize then
              fostruct ← minimizeModel solver solverName fostruct (kill := kill)
            trace[sauto.model] "{fostruct}"
            return .Sat fostruct
          -- Non-Z3 solver
          else
            trace[sauto.model] "Currently, we print readable interpretations only for Z3. For other solvers, we only return the raw model."
            trace[sauto.model] "Model:\n{model}"
            if kill then
              solver.kill
            return .Sat .none
        else
          if kill then
              solver.kill
          return .Sat .none
    | .Unsat =>
        trace[sauto.result] "{solverName} says Unsat"
        let unsatCore ← getUnsatCore solver (kill := kill)
        trace[sauto.result] "Unsat core: {unsatCore}"
        -- trace[sauto] "stderr:\n{stderr}"
        return .Unsat unsatCore
    | .Unknown reason =>
        trace[sauto.result] "{solverName} says Unknown ({reason})"
        if retries > 0 then
          match solverToTryOnUnknown solverName with
          | some s => do
            if kill then
              solver.kill
            trace[sauto.result] "Retrying the query with {s}"
            -- querySolver goalQuery timeout (forceSolver := some s) (retryOnFailure := false) minimize
            getSolverResult solver s minimize kill (retries - 1)
          | none =>
            if kill then
              solver.kill
            return .Unknown reason
        else
          if kill then
            solver.kill
          return .Unknown reason
termination_by retries
