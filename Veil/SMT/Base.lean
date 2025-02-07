import Lean

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

/- FIXME: we really should merge `CheckSatResult` and `SmtResult` -/

inductive CheckSatResult
  | Sat
  | Unsat
  | Unknown (reason : String)
  | Failure (reason : String)
deriving BEq, Inhabited

instance : ToString CheckSatResult where
  toString
    | CheckSatResult.Sat => "sat"
    | CheckSatResult.Unsat => "unsat"
    | CheckSatResult.Unknown r => s!"unknown ({r})"
    | CheckSatResult.Failure r => s!"failure ({r})"
