import Lean
import Auto
import Smt

import LeanSts.SMT.Model

open Lean hiding Command

initialize
  registerTraceClass `sauto
  registerTraceClass `sauto.query
  registerTraceClass `sauto.result
  registerTraceClass `sauto.debug

open Auto.Solver.SMT in
register_option sauto.smt.solver : SolverName := {
  defValue := SolverName.z3
  descr := "SMT solver to use"
}

register_option sauto.smt.macrofinder : Bool := {
  defValue := False
  descr := "Whether to use Z3's macro-finder tactic"
}

inductive SmtResult
  | Sat (model : FirstOrderStructure)
  | Unsat (unsatCore : Auto.Parser.SMTSexp.Sexp)
  | Unknown

namespace Smt
open Elab Tactic Qq

open Smt Smt.Tactic Translate in
def prepareQuery (mv : MVarId) (hs : List Expr) : MetaM String := mv.withContext do
  let mv ← Util.rewriteIffMeta mv
  let goalType : Q(Prop) ← mv.getType
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs (← mv.getType)
  let cmdString := s!"{Command.cmdsAsQuery cmds}"
  trace[sauto.debug] "goal:\n{goalType}"
  -- trace[sauto] "query:\n{cmdString}"
  return cmdString

open Auto Auto.Solver.SMT
def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[sauto.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def emitCommand (p : SolverProc) (c : IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p s!"{c}\n"

def createSolver (name : SolverName) (timeout : Option Nat) : MetaM SolverProc := do
  let tlim ← match timeout with
  | none => pure (auto.smt.timeout.get (← getOptions))
  | some t => pure t
  match name with
  | .none => throwError "createSolver :: Unexpected error"
  -- | .z3   => createAux "z3" #["-in", "-smt2", s!"-T:{tlim}"]
  | .z3   => createAux "z3model.py" #[s!"--tlimit={tlim}"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 => createAux "cvc5" #[s!"--tlimit={tlim * 1000}", "--produce-models"]
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

def querySolver (goalQuery : String) (timeout : Option Nat) : MetaM SmtResult := do
  let opts ← getOptions
  let solverName := sauto.smt.solver.get opts
  trace[sauto.debug] "solver: {solverName}"
  let solver ← createSolver solverName timeout
  if solverName == SolverName.cvc5 then
    emitCommand solver (.setLogic "ALL")
  -- emitCommand solver (.setOption (.produceProofs true))
  -- emitCommand solver (.setOption (.produceUnsatCores true))
  emitCommandStr solver goalQuery
  if sauto.smt.macrofinder.get opts then
    emitCommandStr solver "(check-sat-using (then macro-finder smt))\n"
  else
    emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  let (checkSatResponse, _) ← getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
      emitCommand solver .getModel
      let (_, solver) ← solver.takeStdin
      let stdout ← solver.stdout.readToEnd
      -- let stderr ← solver.stderr.readToEnd
      let (model, _) ← getSexp stdout
      trace[sauto.result] "{solverName} says Sat"
      trace[sauto.debug] "Model:\n{model}"
      let fostruct ← extractStructure model
      trace[sauto.result] "{fostruct}"
      -- trace[sauto] "stderr:\n{stderr}"
      solver.kill
      return .Sat fostruct
  | .atom (.symb "unsat") =>
      emitCommand solver .getUnsatCore
      let (_, solver) ← solver.takeStdin
      let stdout ← solver.stdout.readToEnd
      -- let stderr ← solver.stderr.readToEnd
      let (unsatCore, _stdout) ← getSexp stdout
      solver.kill
      trace[sauto.result] "{solverName} says Unsat"
      trace[sauto.result] "Unsat core: {unsatCore}"
      -- trace[sauto] "Proof:\n{_stdout}"
      -- trace[sauto] "stderr:\n{stderr}"
      return .Unsat unsatCore
  | _ => return .Unknown

-- /-- Our own version of the `smt` & `auto` tactics. -/
syntax (name := sauto) "sauto" smtHints smtTimeout : tactic

@[tactic sauto] def evalSauto : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let hs ← Tactic.parseHints ⟨stx[1]⟩
  let timeout ← Tactic.parseTimeout ⟨stx[2]⟩
  let cmdString ← prepareQuery mv hs
  let res ← querySolver cmdString timeout
  match res with
  | .Sat _ => throwError "the goal is false"
  | .Unknown => throwError "the solver returned unknown"
  | .Unsat _ => mv.admit

end Smt
