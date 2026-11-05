module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Model
public meta import Veil.Core.Tools.Synthesizer.Solver

/-!
# The search monad

This file defines the configuration, state and outcomes of a UPDR run, and the monad `SearchM`
in which the search asks its queries.

## Main definitions

* `Veil.Synthesizer.Config`: the parameters of a run.
* `Veil.Synthesizer.Outcome`: what a run found.
* `Veil.Synthesizer.SearchM`: the search monad, over the frames of the run.
* `Veil.Synthesizer.SearchM.ask`: ask a query, counting fuel and time.

## Implementation notes

`F₀` is `init` and is never stored; `frames[i]` holds the strengthening clauses of `F_{i+1}`, and
every frame implicitly includes the property `P`.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil

/-- A clause admitted into a frame, with its term and whether a trusted solver answered one of
the queries that admitted it. -/
structure Admitted where
  clause : Clause
  term : Term
  viaTrust : Bool

/-- Which generalizer proposes the clause that blocks a counterexample. -/
inductive GeneralizerKind where
  /-- The paper's: unsat cores, then deletion of literals of the negated diagram. -/
  | updr
  /-- Linear templates over the integer individuals (`Linear.candidates`), then `updr`. -/
  | linear
deriving BEq, Repr, Inhabited

/-- The parameters of a run. -/
structure Config where
  /-- The number of solver calls. -/
  fuel : Nat := 5000
  generalizer : GeneralizerKind := .linear
  /-- The number of linear candidates tried per counterexample. -/
  maxLinear : Nat := 24
  /-- Start generalization from the solver's unsat cores, instead of the full negated diagram. -/
  cores : Bool := true
  /-- The length of the longest execution sampled for the linear templates. -/
  sampleDepth : Nat := 3
  /-- The number of frames. -/
  maxFrames : Nat := 40
  /-- Drop literals from blocking clauses. -/
  generalize : Bool := true
  /-- Include the module's declared invariants in the property. -/
  useDeclaredInvariants : Bool := false
  /-- Report each step as a message. -/
  verbose : Bool := false
  /-- Append one JSON object per event to this file. -/
  logFile : Option System.FilePath := none

/-- The counts of a run. -/
structure RunStats where
  /-- The solver calls made. -/
  solverCalls : Nat := 0
  /-- The wall-clock milliseconds of those calls. -/
  solverMs : Nat := 0
  /-- The wall-clock milliseconds by phase. -/
  phases : QueryPhases := {}
deriving Repr, Inhabited

/-- What the bounded path check said about an abstract counterexample that reached `init`. -/
inductive BoundedCheck where
  /-- Not asked: the chain is rooted above level 0. -/
  | notAsked
  /-- No execution of `steps` transitions violates the property. -/
  | noPath (steps : Nat)
  /-- No answer about executions of `steps` transitions. -/
  | noAnswer (steps : Nat) (reason : String)

/-- What a run found. -/
inductive Outcome where
  /-- The clauses, with `P`, form an inductive invariant at `frame`. -/
  | foundInvariant (frame : Nat) (clauses : Array Admitted) (anyTrusted : Bool)
  /-- An execution from `init` to a state violating `P`. -/
  | «unsafe» (path : DecodedTrace)
  /-- A violation after `steps` transitions whose model could not be decoded. -/
  | unsafeUndecoded (steps : Nat) (reason : String)
  /-- An abstract counterexample that no universal clause can block, from the structure contained
  in an initial state to the one with a successor violating `P` [Karbyshev et al., Prop. 5.6]. -/
  | noUniversalInvariant (diagrams : Array FinStructure) (check : BoundedCheck)
  /-- An abstract counterexample in a module with integer state, for which the verdict of
  `noUniversalInvariant` is not given. `frameSizes` counts the clauses of each frame. -/
  | absenceWithheld (diagrams : Array FinStructure) (check : BoundedCheck) (frameSizes : Array Nat)
  /-- The search stopped without a verdict. -/
  | unknown (reason : String) (frameSizes : Array Nat)
  /-- The search threw an exception: a bug, not a solver limit. -/
  | internalError (message : String) (frameSizes : Array Nat)

/-- The reason the log gives for `Outcome.absenceWithheld`. -/
def absenceWithheldReason : String :=
  "the search closed without an invariant; the no-universal-invariant verdict is established \
    only for vocabularies without integers (Proposition 5.6 of the paper is about uninterpreted \
    sorts)"

/-- The result of a run. -/
structure RunResult where
  outcome : Outcome
  stats : RunStats
  /-- The progress lines of the run. -/
  log : Array String

/-- The read-only data of a run. -/
structure Ctx where
  cfg : Config
  qctx : QueryCtx
  sig : Signature
  /-- The conjuncts of the property `P`. -/
  property : Array Term
  /-- The conjuncts of `P` with their capitals quantified. -/
  propertyConjuncts : Array Term
  /-- The conjunction of `propertyConjuncts`. -/
  propertyTerm : Term

/-- The state of a run. -/
structure St where
  /-- `frames[i]` holds the strengthening clauses of `F_{i+1}`. -/
  frames : Array (Array Admitted) := #[#[]]
  /-- The solver calls left. -/
  fuel : Nat
  log : Array String := #[]
  stats : RunStats := {}
  /-- Whether some `unsat` answer came from a trusted solver. -/
  anyTrusted : Bool := false
  /-- Whether a write to the log file failed. -/
  logFileFailed : Bool := false
  /-- The structure last blocked at the frontier; a frontier query returning it again is a bug. -/
  lastFrontier : Option FinStructure := none
  /-- States known to be reachable, each with the number of transitions that reached it. -/
  samples : Array (FinStructure × Nat) := #[]

/-- The search monad. -/
abbrev SearchM := ReaderT Ctx (StateRefT St TermElabM)

/-- A clause as a JSON object for the log. -/
def clauseJson (c : Clause) : Json :=
  Json.mkObj [("text", toString c), ("numVars", c.vars.size), ("numLits", c.lits.size)]

/-- Append a JSON object as a line of a file, creating its directory. -/
def appendEvent (path : System.FilePath) (j : Json) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.withFile path .append (·.putStrLn j.compress)

namespace SearchM

/-- Record a progress line, shown as a message under `verbose`. -/
def say (msg : String) : SearchM Unit := do
  modify fun s ↦ { s with log := s.log.push msg }
  if (← read).cfg.verbose then logInfo msg

/-- Append an event to the log file, if there is one. A failed write is reported once. -/
def event (kind : String) (fields : List (String × Json)) : SearchM Unit := do
  let some path := (← read).cfg.logFile | return
  try appendEvent path (Json.mkObj (("event", kind) :: fields))
  catch e =>
    unless (← get).logFileFailed do
      logWarning m!"IC3: could not append to the log file {path}: {e.toMessageData}; later \
        events are not logged"
      modify fun s ↦ { s with logFileFailed := true }

/-- The number of strengthening clauses of each frame. -/
def frameSizes : SearchM (Array Nat) := return (← get).frames.map (·.size)

/-- The `unknown` outcome. -/
def stop (reason : String) : SearchM Outcome := return .unknown reason (← frameSizes)

/-- Record reachable states with their depths; a known state keeps the smaller depth. -/
def addSamples (σs : Array (FinStructure × Nat)) : SearchM Unit := modify fun s ↦
  { s with samples := σs.foldl (init := s.samples) fun acc (σ, d) ↦
      match acc.findIdx? (·.1 == σ) with
      | some i => if d < acc[i]!.2 then acc.set! i (σ, d) else acc
      | none => acc.push (σ, d) }

/-- The samples of depth at most `j`. -/
def samplesUpTo (j : Nat) : SearchM (Array FinStructure) :=
  return ((← get).samples.filter (·.2 ≤ j)).map (·.1)

/-- The clauses of `F_i`, `i ≥ 1`, with the property. -/
def frameTerms (i : Nat) : SearchM (Array Term) := do
  return (← read).property ++ ((← get).frames[i - 1]?.getD #[]).map (·.term)

/-- Whether some clause of `F_i`, `i ≥ 1`, subsumes `c`. -/
def frameSubsumes (i : Nat) (c : Clause) : SearchM Bool :=
  return ((← get).frames[i - 1]?.getD #[]).any (·.clause.subsumes c)

/-- Add `a` to `F₁ … F_j`, keeping each frame free of subsumed clauses. -/
def addClause (j : Nat) (a : Admitted) : SearchM Unit := modify fun s ↦
  { s with frames := (Array.range j).foldl (init := s.frames) fun fr i ↦
      if i < fr.size then fr.modify i (Clause.insertSubsuming (·.clause) · a) else fr }

/-- Consume one solver call; `false` when none is left. -/
def spend : SearchM Bool := do
  let s ← get
  if s.fuel == 0 then return false
  set { s with fuel := s.fuel - 1 }
  return true

/-- Discharge a statement, counting the call and its time. -/
def runCounted (stmt : Term) (steps coreLits : Nat) (wantModel : Bool) :
    SearchM (QueryResult × Option (Array Nat)) := do
  unless ← spend do return (.unknown s!"fuel exhausted ({(← read).cfg.fuel} solver calls)", none)
  let t0 ← IO.monoMsNow
  let r ← runStatement (← read).qctx.mod stmt steps coreLits wantModel
  let dt := (← IO.monoMsNow) - t0
  modify fun s ↦ { s with
    stats.solverCalls := s.stats.solverCalls + 1, stats.solverMs := s.stats.solverMs + dt
    anyTrusted := s.anyTrusted || r.1.isTrusted }
  return r

/-- Ask query `q`, with the unsat core of its `coreLits` trailing diagram literals. With `retry`,
an answer the solver gave up on is asked once more with twice `veil.smt.timeout`. -/
def askCore (q : Query) (coreLits : Nat := 0) (wantModel : Bool := true) (retry : Bool := false) :
    SearchM (QueryResult × Option (Array Nat)) := do
  let qctx := (← read).qctx
  let stmt ← qctx.statement (← if q.steps > 0 then qctx.normalizedTr? else pure none) q
  let r ← runCounted stmt q.steps coreLits wantModel
  unless retry && r.1.solverGaveUp do return r
  let t := veil.smt.timeout.get (← getOptions)
  if (← get).fuel == 0 then
    return (.unknown s!"fuel exhausted ({(← read).cfg.fuel} solver calls)", none)
  say s!"the solver gave up ({(toString r.1).take 120}); asking again with veil.smt.timeout {2 * t}"
  withOptions (veil.smt.timeout.set · (2 * t)) (runCounted stmt q.steps coreLits wantModel)

/-- Ask query `q`. -/
def ask (q : Query) (wantModel : Bool := true) (retry : Bool := false) : SearchM QueryResult :=
  (·.1) <$> askCore q (wantModel := wantModel) (retry := retry)

/-- `F_{j-1} ∧ tr ∧ ¬post'`: a predecessor in `F_{j-1}` of a state violating `post`. -/
def stepQuery (j : Nat) (post : Term) (wantModel : Bool := true) : SearchM QueryResult := do
  if j == 0 then throwError "IC3: predecessor query below frame 0"
  let frame ← if j == 1 then pure #[] else frameTerms (j - 1)
  ask { init := j == 1, frame, steps := 1, goal := .violates post } wantModel

/-- `init ∧ ¬post`. -/
def initQuery (post : Term) (wantModel : Bool := true) (retry : Bool := false) :
    SearchM QueryResult :=
  ask { init := true, goal := .violates post } wantModel retry

/-- Ask `query p` for each conjunct `p` of the property, stopping at the first answer that is
not `unsat`, and otherwise returning the last. -/
def perConjunct (query : Term → SearchM QueryResult) : SearchM QueryResult := do
  let mut last := none
  for p in (← read).propertyConjuncts do
    let r ← query p
    unless r matches .unsat .. do return r
    last := some r
  let some r := last | throwError "IC3: the property has no conjuncts"
  return r

/-- Decode a model over the run's signature. -/
def decode (j : Json) : SearchM DecodedTrace := do
  match decodeTrace (← read).sig j with
  | .ok dt =>
    unless dt.completed.isEmpty do
      trace[veil.synthesizer.debug] "IC3: the model did not mention {dt.completed}; default \
        tables were used"
    return dt
  | .error e => throwError "IC3: could not decode a solver model: {e}"

/-- The outcome of a `sat` answer that is an execution of `steps` transitions violating `P`. -/
def violation (steps : Nat) (r : QueryResult) : SearchM Outcome := do
  match r with
  | .sat m =>
    try return .«unsafe» (← decode m)
    catch e => return .unsafeUndecoded steps ((← e.toMessageData.toString).take 300).toString
  | .satUndecoded reason => return .unsafeUndecoded steps reason
  | _ => throwError "IC3: a violation was reported from an answer that is not sat ({r})"

end SearchM

end Veil.Synthesizer
