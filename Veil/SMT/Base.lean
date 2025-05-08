import Lean
import Veil.SMT.Model

/-- Package to use for translating Lean goals to SMT-LIB queries. -/
inductive SmtTranslator
  | leanSmt
  | leanAuto
deriving BEq, Hashable, Inhabited

instance : ToString SmtTranslator where
  toString : SmtTranslator → String
  | .leanSmt  => "lean-smt"
  | .leanAuto => "lean-auto"

instance : Lean.KVMap.Value SmtTranslator where
  toDataValue n := toString n
  ofDataValue?
  | "lean-smt"  => some .leanSmt
  | "lean-auto" => some .leanAuto
  | _           => none

inductive SmtSolver where
  | z3
  | cvc5
deriving BEq, Hashable, Inhabited

instance : ToString SmtSolver where
  toString
    | SmtSolver.z3  => "z3"
    | SmtSolver.cvc5 => "cvc5"

instance : Lean.KVMap.Value SmtSolver where
  toDataValue n := toString n
  ofDataValue?
  | "z3"  => some .z3
  | "cvc5" => some .cvc5
  | _     => none

/-- If the solver returns `Unknown`, we try the other solver. -/
def solverToTryOnUnknown (tried : SmtSolver) : SmtSolver :=
  match tried with
  | .z3 => SmtSolver.cvc5
  | .cvc5 => SmtSolver.z3

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

inductive SmtResult
  /-- `modelString` contains the raw string returned by the solver. -/
  | Sat (modelString : Option String)
  | Unsat
  | Unknown (reason : Option String)
  | Failure (reason : Option String)
deriving Inhabited

instance : ToString SmtResult where
  toString
    | SmtResult.Sat none => "sat"
    | SmtResult.Sat (some m) => s!"sat\n{m}"
    | SmtResult.Unsat => s!"unsat"
    | SmtResult.Unknown none => s!"unknown"
    | SmtResult.Unknown (some r) => s!"unknown ({r})"
    | SmtResult.Failure none => "failure"
    | SmtResult.Failure (some r) => s!"failure ({r})"

open Lean in
instance : ToJson SmtResult where
  toJson res := match res with
    | .Sat none => Json.arr #["sat"]
    | .Unsat => Json.arr #["unsat"]
    | .Unknown none => Json.arr #["unknown"]
    | .Failure none => Json.arr #["failure"]

    | .Sat (some m) => Json.arr #["sat", m]
    | .Unknown (some r) => Json.arr #["unknown", r]
    | .Failure (some r) => Json.arr #["failure", r]


open Lean in
instance : FromJson SmtResult where
  fromJson? s := match s with
    | Json.arr #["sat"] => .ok (.Sat none)
    | Json.arr #["unsat"] => .ok .Unsat
    | Json.arr #["unknown"] => .ok (.Unknown none)
    | Json.arr #["failure"] => .ok (.Failure none)
    | Json.arr #["sat", m] => fromJsonStr? m >>= fun m => .ok (.Sat (some m))
    | Json.arr #["unknown", r] => fromJsonStr? r >>= fun r => .ok (.Unknown (some r))
    | Json.arr #["failure", r] => fromJsonStr? r >>= fun r => .ok (.Failure (some r))
    | _ => .error s!"invalid SMT result: {s}"
    where
      fromJsonStr? : Json → Except String String
        | Json.str s => .ok s
        | s => .error s!"expected string, got {s}"

abbrev SExpression := Auto.Parser.SMTSexp.Sexp

abbrev TimeInMs := Nat
