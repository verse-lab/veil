import Veil.Base
import Veil.SMT.Translation

partial def Handle.readLineSkip (h : IO.FS.Handle) (skipLine : String := "\n") : IO String := do
  let rec loop := do
    let line ← h.getLine
    if line.isEmpty then
      return line
    if line == skipLine then
      loop
    else
      return line
  loop

partial def Handle.readUntil (h : IO.FS.Handle) (endString : String) : IO String := do
  let rec loop (s : String) := do
    let line ← h.getLine
    if line.isEmpty then
      return s
    else if line == endString then
      return (s ++ line)
    else
      loop (s ++ line)
  loop ""

namespace Veil.SMT

open Lean hiding Command Declaration

def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[veil.smt.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def emitCommand (p : SolverProc) (c : Auto.IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p s!"{c}\n"

def createSolver (name : SmtSolver) (withTimeout : Nat) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  let seed := veil.smt.seed.get $ ← getOptions
  match name with
  | .z3   => createAux "z3" #["-in", "-smt2", s!"-t:{tlim_sec * 1000}", s!"sat.random_seed={seed}", s!"smt.random_seed={seed}"]
  | .cvc5 =>
      let args := #["--lang", "smt", s!"--tlimit-per={tlim_sec * 1000}", "--seed", s!"{seed}",
        "--finite-model-find", "--enum-inst-interleave", "--nl-ext-tplanes", "--incremental"]
      let proc ← createAux "cvc5" args
      emitCommand proc (.setLogic "ALL")
      pure proc
where
  createAux (path : String) (args : Array String) : MetaM SolverProc := do
    trace[veil.smt.debug] "invoking {path} {args}"
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

open Smt Smt.Tactic Translate in
partial def querySolver (goalQuery : String) (withTimeout : Nat) (forceSolver : Option SmtSolver := none) (retryOnUnknown : Bool := false) (getModel? : Bool := true) (minimize : Option Bool := none) : MetaM SmtResult := do
  withTraceNode `veil.smt.perf.query (fun _ => return "querySolver") do
  try
  let opts ← getOptions
  let minimize := minimize.getD (veil.smt.model.minimize.get opts)
  let solverName :=
    match forceSolver with
    | some s => s
    | none => veil.smt.solver.get opts
  trace[veil.smt.debug] "solver: {solverName}"
  let solver ← createSolver solverName withTimeout
  emitCommandStr solver goalQuery
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  trace[veil.smt.debug] "[checkSat] stdout: {stdout}"
  let (checkSatResponse, _) ← Auto.Solver.SMT.getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    trace[veil.smt.result] "{solverName} says Sat"
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[veil.smt.debug] "stdout: {stdout}"
    trace[veil.smt.debug] "stderr: {stderr}"
    let (model, _) ← Auto.Solver.SMT.getSexp stdout
    solver.kill
    return SmtResult.Sat s!"{model}" .none

  | .atom (.symb "unsat") =>
    trace[veil.smt.result] "{solverName} says Unsat"
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[veil.smt.debug] "stdout: {stdout}"
    trace[veil.smt.debug] "stderr: {stderr}"
    solver.kill
    return SmtResult.Unsat

  | .atom (.symb "unknown") =>
    trace[veil.smt.result] "{solverName} says Unknown"
      if retryOnUnknown then
        let newSolver := solverToTryOnUnknown solverName
        trace[veil.smt.debug] "Retrying with {newSolver}"
        querySolver goalQuery withTimeout (forceSolver := .some newSolver) (retryOnUnknown := false) getModel? minimize
      else
        let (_, solver) ← solver.takeStdin
        let stdout ← solver.stdout.readToEnd
        let stderr ← solver.stderr.readToEnd
        trace[veil.smt.debug] "stdout: {stdout}"
        trace[veil.smt.debug] "stderr: {stderr}"
        solver.kill
        return SmtResult.Unknown .none

  | _ => throwError s!"Unexpected response from solver: {checkSatResponse}"
  catch e =>
    let exMsg ← e.toMessageData.toString
    return .Failure s!"{exMsg}"

end Veil.SMT
