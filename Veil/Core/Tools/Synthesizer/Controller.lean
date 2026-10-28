module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Generalize

/-!
# The UPDR loop

This file implements UPDR [Karbyshev et al.] in the proof-obligation formulation of PDR.

An *obligation* `(j, σ)` is a structure `σ` that frame `F_j` must exclude: a state containing `σ`
reaches a violation of `P` in `N - j + 1` steps. While the frontier `F_N` has a state with a
successor violating `P`, that state becomes the obligation `(N, σ)`. An obligation is discharged by
asking for a predecessor of `Diag(σ)` in `F_{j-1}`: a predecessor becomes the obligation
`(j - 1, σ')`; without one, the generalized `¬ Diag(σ)` is added to `F₁ … F_j`. When the frontier
is clear, `F_{N+1}` is opened and the clauses inductive relative to their frame are pushed forward;
two equal frames are an inductive invariant. A chain of obligations that reaches the initial
states means that no universal inductive invariant proves `P` [Karbyshev et al., Prop. 5.6].

## Main definitions

* `Veil.Synthesizer.SearchM.discharge`: discharge a stack of obligations.
* `Veil.Synthesizer.SearchM.propagate`: push clauses forward and detect a fixpoint.
* `Veil.Synthesizer.synthesize`: run UPDR on a module's property.

## Implementation notes

* The frontier query and the two initial checks ask about one conjunct of `P` at a time, as
  `#check_invariants` does.
* A query whose answer the search cannot do without is asked again with twice
  `veil.smt.timeout` when the solver gives up (`SearchM.askCore`).
* The invariant and counterexample verdicts are re-established by the certificates; a bug here can
  make a certificate fail but not a theorem false. The no-universal-invariant verdict rests on this
  code and on Proposition 5.6 of the paper, extended to function symbols and enum sorts: a
  universal sentence passes to substructures closed under the functions, and an enum carrier is
  fixed. With integer state in the vocabulary no such verdict is given (`Outcome.absenceWithheld`).

## References

* A. Karbyshev, N. Bjørner, S. Itzhaky, N. Rinetzky, S. Shoham, *Property-Directed Inference of
  Universal Invariants or Proving Their Absence*, Journal of the ACM 64(1), 2017.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil

/-- An obligation: frame `level` must exclude `σ`. `lastPredecessor` is the predecessor last found
for it, which a correct model of the next predecessor query cannot be. -/
structure Obligation where
  level : Nat
  σ : FinStructure
  lastPredecessor : Option FinStructure := none

namespace SearchM

/-- A clause of `F_{j-1}` that `σ` violates and that is inductive relative to `F_{j-1}`, which
blocks `σ` at `F_j` with one query. At most two clauses are tried, newest first. -/
def reuseFromBelow (j : Nat) (σ : FinStructure) : SearchM (Option Admitted) := do
  if j < 2 then return none
  let mut tries := 0
  for a in ((← get).frames[j - 2]?.getD #[]).reverse do
    if tries ≥ 2 then break
    if σ.models a.clause || (← frameSubsumes j a.clause) then continue
    tries := tries + 1
    let r ← stepQuery j a.term (wantModel := false)
    if r matches .unsat .. then return some { a with viaTrust := a.viaTrust || r.isTrusted }
  return none

/-- The outcome of an abstract counterexample `diagrams` that reaches `init` at level `j`. Rooted
at level 0, it describes an execution of `N + 1` transitions, which a bounded query checks. -/
def analyzeCounterexample (N j : Nat) (diagrams : Array FinStructure) : SearchM Outcome := do
  let ctx ← read
  let mut check := BoundedCheck.notAsked
  if j == 0 then
    let k := N + 1
    say s!"bounded path check of length {k}"
    let q : Query := { init := true, steps := k, goal := .violates ctx.propertyTerm }
    match ← ask q (retry := true) with
    | r@(.sat _) | r@(.satUndecoded _) => return ← violation k r
    | .unsat .. => check := .noPath k
    | .unknown r =>
      say s!"bounded path check returned unknown ({r}); the abstract counterexample stands"
      check := .noAnswer k s!"unknown: {r}"
    | .error e =>
      say s!"bounded path check failed ({e}); the abstract counterexample stands"
      check := .noAnswer k s!"error: {e}"
  if ctx.sig.numericSorts.isEmpty then return .noUniversalInvariant diagrams check
  return .absenceWithheld diagrams check (← frameSizes)

/-- Block `σ` at level `j ≥ 1`, which has no predecessor in `F_{j-1}`: generalize `¬ Diag(σ)`, or
report the abstract counterexample `stack` when `Diag(σ)` meets `init`. The unsat core `kCore`
and answer `kRes` are those of the predecessor query. -/
def block (N j : Nat) (σ : FinStructure) (stack : List Obligation) (kRes : QueryResult)
    (kCore : Option (Array Nat)) : SearchM (Option Outcome) := do
  let diag := σ.negatedDiagram
  let lits ← σ.diagramLiterals.mapM Literal.toTerm
  let (iRes, iCore) ← askCore { init := true, goal := .diagram diag.vars lits } lits.size
    (wantModel := false) (retry := true)
  match iRes with
  | .sat _ | .satUndecoded _ =>
    say s!"level {j}: Diag(σ) meets init"
    return some (← analyzeCounterexample N j (stack.map (·.σ)).toArray)
  | .unknown r => return some (← stop s!"init check unknown: {r}")
  | .error e => return some (← stop s!"init check failed: {e}")
  | .unsat .. => pure ()
  let (c, i, k) ← generalize j σ diag iRes kRes iCore kCore
  if σ.models c then
    throwError "IC3: the admitted clause does not exclude the structure it was cut from ({c}); a \
      generalizer produced a clause outside the negated diagram"
  event "admitted" [("level", j), ("frontier", N), ("diagram", clauseJson diag),
    ("clause", clauseJson c), ("frameSizes", toJson (← frameSizes))]
  say s!"level {j}: admitted ({c.lits.size} of {diag.lits.size} literals kept) {c}"
  addClause j { clause := c, term := ← c.toTerm, viaTrust := i.isTrusted || k.isTrusted }
  return none

/-- Discharge a stack of obligations against the frontier `F_N`. -/
partial def discharge (N : Nat) : List Obligation → SearchM (Option Outcome)
  | [] => return none
  | stack@(ob :: rest) => do
    let (j, σ) := (ob.level, ob.σ)
    -- A level-0 structure came from a predecessor query against `init`.
    if j == 0 then
      say "level 0: the structure is contained in an initial state"
      return some (← analyzeCounterexample N 0 (stack.map (·.σ)).toArray)
    if let some a ← reuseFromBelow j σ then
      say s!"level {j}: reused {a.clause}"
      event "reused" [("level", j), ("frontier", N), ("diagram", clauseJson σ.negatedDiagram),
        ("clause", clauseJson a.clause)]
      addClause j a
      return ← discharge N rest
    let lits ← σ.diagramLiterals.mapM Literal.toTerm
    let frame ← if j == 1 then pure #[] else frameTerms (j - 1)
    let q : Query :=
      { init := j == 1, frame, steps := 1, goal := .diagram σ.negatedDiagram.vars lits }
    let (kRes, kCore) ← askCore q lits.size (retry := true)
    match kRes with
    | .sat m =>
      let dt ← decode m
      let σ' := dt.states[0]!
      if ob.lastPredecessor == some σ' then
        throwError "IC3: the predecessor query returned the structure just blocked at level \
          {j - 1}; a model symbol was decoded or completed wrongly"
      -- At level one both states of the model are reachable.
      if j == 1 && dt.states.size ≥ 2 then addSamples #[(dt.states[0]!, 0), (dt.states[1]!, 1)]
      say s!"level {j}: predecessor found in F_{j-1}; descending"
      discharge N ({ level := j - 1, σ := σ' } :: { ob with lastPredecessor := some σ' } :: rest)
    | .satUndecoded r =>
      return some (← stop
        s!"predecessor query answered sat, but its model could not be decoded: {r}")
    | .unknown r => return some (← stop s!"predecessor query unknown: {r}")
    | .error e => return some (← stop s!"predecessor query failed: {e}")
    | .unsat .. =>
      match ← block N j σ stack kRes kCore with
      | some o => return some o
      | none => discharge N rest

/-- Push each clause of `F_i` that is inductive relative to `F_i` into `F_{i+1}`, for `i ≤ N`.
Returns the first `i` whose clauses all moved, so that `F_i = F_{i+1}` is inductive. -/
def propagate (N : Nat) : SearchM (Option Nat) := do
  for i in [1:N+1] do
    let mut allPushed := true
    for a in (← get).frames[i - 1]?.getD #[] do
      if ← frameSubsumes (i + 1) a.clause then continue
      let q : Query := { frame := ← frameTerms i, steps := 1, goal := .violates a.term }
      let r ← ask q (wantModel := false)
      if r matches .unsat .. then
        let a := { a with viaTrust := a.viaTrust || r.isTrusted }
        modify fun s ↦
          { s with frames := s.frames.modify i (Clause.insertSubsuming (·.clause) · a) }
      else allPushed := false
    if allPushed then return some i
  return none

/-- Block every bad state of the frontier `F_N`, then open `F_{N+1}` and propagate, until a
fixpoint or a verdict. -/
partial def mainLoop (N : Nat) : SearchM Outcome := do
  let ctx ← read
  if N > ctx.cfg.maxFrames then return ← stop s!"frame limit reached ({ctx.cfg.maxFrames} frames)"
  let frame ← frameTerms N
  match ← perConjunct (ask { frame, steps := 1, goal := .violates · } (retry := true)) with
  | .sat m =>
    let σ := (← decode m).states[0]!
    if (← get).lastFrontier == some σ then
      throwError "IC3: the frontier query returned the structure just blocked; a model symbol was \
        decoded or completed wrongly"
    modify fun s ↦ { s with lastFrontier := some σ }
    say s!"frame {N}: bad state found; blocking"
    match ← discharge N [{ level := N, σ }] with
    | some outcome => return outcome
    | none => mainLoop N
  | .satUndecoded r => stop s!"frontier query answered sat, but its model could not be decoded: {r}"
  | .unknown r => stop s!"frontier query unknown: {r}"
  | .error e => stop s!"frontier query failed: {e}"
  | .unsat .. =>
    say s!"frame {N} is clear; opening frame {N + 1}"
    event "frame_clear" [("frame", N), ("frameSizes", toJson (← frameSizes))]
    modify fun s ↦ { s with frames := s.frames.push #[], lastFrontier := none }
    let some i ← propagate N | mainLoop (N + 1)
    say s!"frame {i} equals frame {i + 1}: fixpoint"
    let s ← get
    return .foundInvariant i (Clause.removeSubsumed (·.clause) s.frames[i - 1]!) s.anyTrusted

/-- Record the states of one execution of each length up to `sampleDepth` as reachable samples
for the linear templates. A failure only leaves fewer samples. -/
def collectSamples : SearchM Unit := do
  let sample (k : Nat) : SearchM Unit := do
    try
      let q : Query := { init := true, steps := k, goal := .violates (← `(False)) }
      match ← ask q with
      | .sat m => addSamples ((← decode m).states.mapIdx fun i σ ↦ (σ, i))
      | .unsat .. => say s!"no reachable sample of length {k}: no execution of that length"
      | r => say s!"reachable sample of length {k} not collected ({(toString r).take 160})"
    catch e =>
      let reason := ((← e.toMessageData.toString).take 160).toString
      say s!"reachable sample of length {k} skipped ({reason})"
  for k in [0:(← read).cfg.sampleDepth + 1] do sample k
  say s!"reachable samples for the linear templates: {(← get).samples.size}"

/-- The search: the reachable samples, `init ∧ ¬P` and `init ∧ tr ∧ ¬P'`, then the main loop. -/
def search : SearchM Outcome := do
  let ctx ← read
  if ctx.cfg.generalizer == .linear && !ctx.sig.numericSorts.isEmpty then collectSamples
  match ← perConjunct (initQuery · (retry := true)) with
  | r@(.sat _) | r@(.satUndecoded _) => violation 0 r
  | .unknown r => return .unknown s!"init ∧ ¬P unknown: {r}" #[]
  | .error e => return .unknown s!"init ∧ ¬P failed: {e}" #[]
  | .unsat .. =>
    -- With this check, "frame `N - 1` is clear" holds for `N = 1` too.
    match ← perConjunct (ask { init := true, steps := 1, goal := .violates · } (retry := true)) with
    | r@(.sat _) | r@(.satUndecoded _) => violation 1 r
    | .unknown r => return .unknown s!"init ∧ tr ∧ ¬P' unknown: {r}" #[]
    | .error e => return .unknown s!"init ∧ tr ∧ ¬P' failed: {e}" #[]
    | .unsat .. => mainLoop 1

end SearchM

/-- The conjuncts of the property `P`: the module's `safety` clauses and, with
`useDeclaredInvariants`, its declared `invariant`s. Trusted invariants are not included. -/
def propertyConjuncts (mod : Veil.Module) (cfg : Config) : Array Term :=
  mod.safeties.map (·.term) ++
    if cfg.useDeclaredInvariants then (mod.assertions.filter (·.kind == .invariant)).map (·.term)
    else #[]

/-- The conjuncts of `P`, or an error for a module without any. -/
def checkedProperty (mod : Veil.Module) (cfg : Config) : CoreM (Array Term) := do
  let property := propertyConjuncts mod cfg
  if property.isEmpty then
    throwError "IC3: the module declares no safety property{if cfg.useDeclaredInvariants then ""
      else " (use `(invariants := true)` to work on its declared invariants)"}"
  return property

/-- Run UPDR on a module's property, over its vocabulary `sig`. -/
def synthesize (mod : Veil.Module) (cfg : Config) (sig : Signature) : TermElabM RunResult := do
  let property ← checkedProperty mod cfg
  let propertyConjuncts ← property.mapM fun t ↦ `((uqc% (($t:term) : Prop)))
  let ctx : Ctx :=
    { cfg, qctx := ← QueryCtx.ofModule mod, sig, property, propertyConjuncts
      propertyTerm := ← repeatedAnd propertyConjuncts }
  -- The state lives in a reference, so that the frames survive an exception.
  let ref ← IO.mkRef ({ fuel := cfg.fuel } : St)
  let phases₀ ← queryPhases.get
  -- Each query is bounded by its own budget and the run by fuel; the command's is lifted.
  let outcome ← withTheReader Core.Context (fun c ↦ { c with maxHeartbeats := 0 }) <|
    tryCatchRuntimeEx (SearchM.search.run ctx ref) fun e ↦ do
      return .internalError ((← e.toMessageData.toString).take 400).toString
        ((← ref.get).frames.map (·.size))
  let s ← ref.get
  let phases := (← queryPhases.get).sub phases₀
  return { outcome, stats := { s.stats with phases }, log := s.log }

end Veil.Synthesizer
