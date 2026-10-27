module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Linear
public meta import Veil.Core.Tools.Synthesizer.Search

/-!
# Generalization

Blocking a structure `σ` at frame `j` adds the negated diagram `¬ Diag(σ)` to `F₁ … F_j`. This
file generalizes that clause: it looks for a subclause that is still *admissible*, that is,
initial (`init ∧ ¬c` is unsatisfiable) and without a predecessor in `F_{j-1}`
(`F_{j-1} ∧ tr ∧ ¬c'` is unsatisfiable) [Karbyshev et al., Section 4.3].

## Main definitions

* `Veil.Synthesizer.SearchM.admit`: decide whether a candidate clause is admissible.
* `Veil.Synthesizer.SearchM.minimize`: drop literals of an admissible clause by group deletion.
* `Veil.Synthesizer.SearchM.generalize`: the generalization of a blocking clause.

## Implementation notes

The passes, in order: linear templates (`Linear.candidates`) on a module with integer state; the
literals the unsat cores of the blocking queries name, then minimization; and, when the cores do
not give an admissible clause, greedy deletion of literals, cheapest first (`literalRank`). A
candidate false in a known reachable state of depth at most `j` is rejected without a solver call.
Every clause that leaves this file passed both admission queries, so the passes affect which
clauses are found and the time taken, not soundness.

## References

* A. Karbyshev, N. Bjørner, S. Itzhaky, N. Rinetzky, S. Shoham, *Property-Directed Inference of
  Universal Invariants or Proving Their Absence*, Journal of the ACM 64(1), 2017.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil

/-- What the admission check says about a candidate clause. -/
inductive Admission where
  /-- Both admission queries answered `unsat`, with these answers. -/
  | admissible (init step : QueryResult)
  /-- Rejected: `sampled_out`, `not_initial` or `has_predecessor`, as the log records it. -/
  | rejected (verdict : String)
  /-- No answer, which is no evidence about the candidate. -/
  | noAnswer

/-- A rejection in words. -/
def Admission.describeRejection : String → String
  | "sampled_out" => "false in a reachable sample"
  | "not_initial" => "not admissible in clause form: an initial state violates it"
  | "has_predecessor" => "not admissible in clause form: it has a predecessor in the frame below"
  | v => v

/-- The order in which generalization drops literals, cheapest first: numerals, then equalities and
class constants, functions, class relations, and the module's own relations. -/
def literalRank (l : Literal) : Nat :=
  match l.atom with
  | .lin .. => if l.atom.isNumeral then 0 else 2
  | .eq .. => 1
  | .rel f _ =>
    match f.origin, f.isFunction with
    | .field _, true => if f.arity == 0 then 1 else 2
    | .component, true => 2
    | .field _, false => 3
    | .component, false => 4

namespace SearchM

/-- Whether candidate `c`, proposed by `generalizer` for the blocking clause `c₀` at level `j`, is
admissible. The verdict is logged. -/
def admit (j : Nat) (c₀ : Clause) (generalizer : String) (c : Clause) : SearchM Admission := do
  let record (verdict : String) (reason := "") : SearchM Unit :=
    event "candidate" [("level", j), ("clause", clauseJson c), ("verdict", verdict),
      ("from", clauseJson c₀), ("generalizer", generalizer), ("reason", reason)]
  let noAnswer (query r : String) : SearchM Admission := do
    say s!"level {j}: no solver answer for candidate {c} ({query}: {r.take 160})"
    record "unknown" s!"{query}: {r.take 300}"
    return .noAnswer
  if (← samplesUpTo j).any (!·.models c) then
    record "sampled_out"
    return .rejected "sampled_out"
  let t ← c.toTerm
  let i ← initQuery t (wantModel := false)
  match i with
  | .sat _ | .satUndecoded _ => record "not_initial"; return .rejected "not_initial"
  | .unknown r | .error r => return ← noAnswer "initiation" r
  | .unsat .. => pure ()
  let k ← stepQuery j t (wantModel := false)
  match k with
  | .sat _ | .satUndecoded _ => record "has_predecessor"; return .rejected "has_predecessor"
  | .unknown r | .error r => return ← noAnswer "consecution" r
  | .unsat .. => pure ()
  record "admissible"
  return .admissible i k

/-- Drop literals of the admissible clause `c`, whose admission answers are `i` and `k`, while it
stays admissible. Literals are tried by rank, cheapest first. Within a rank the remaining literals
are dropped as a group; when the result is not admissible the group is halved and each half is
tried the same way, down to single literals. A group that would empty the clause is halved
without a try, and at most `2 * |c|` tries are made, so that every single literal is still tried.
A missing answer ends the pass. -/
def minimize (j : Nat) (c : Clause) (i k : QueryResult) (check : Clause → SearchM Admission) :
    SearchM (Clause × QueryResult × QueryResult) := do
  let halves (g : Array Nat) : List (Array Nat) :=
    if g.size ≥ 2 then [g.extract 0 (g.size / 2), g.extract (g.size / 2) g.size] else []
  let ranks := ((c.lits.map literalRank).qsort (· < ·)).toList.eraseDups
  let mut answers := (i, k)
  let mut keep := Array.replicate c.lits.size true
  let mut tries := 0
  for r in ranks do
    let mut work := [(Array.range c.lits.size).filter (literalRank c.lits[·]! == r)]
    let mut stopped := false
    while true do
      let g :: rest := work | break
      work := rest
      let g := g.filter (keep[·]!)
      if g.isEmpty then continue
      if g.size ≥ (keep.filter id).size then
        work := halves g ++ work
        continue
      if tries ≥ 2 * c.lits.size then
        stopped := true
        break
      tries := tries + 1
      let keep' := g.foldl (·.set! · false) keep
      match ← check (c.restrict (keep'[·]!)) with
      | .admissible i' k' => keep := keep'; answers := (i', k')
      | .rejected _ => work := halves g ++ work
      | .noAnswer => stopped := true; break
    if stopped then break
  let dropped := (keep.filter (!·)).size
  if dropped > 0 then
    say s!"level {j}: minimization dropped {dropped} more literal(s) in {tries} tries"
  return (c.restrict (keep[·]!), answers)

/-- The first linear template candidate that is admissible, among at most `maxLinear`. -/
def linearPass (j : Nat) (σ : FinStructure) (c₀ : Clause) :
    SearchM (Option (Clause × QueryResult × QueryResult)) := do
  let ctx ← read
  let cands := Linear.candidates σ ctx.sig.numerals ((← get).samples.map (·.1))
  say s!"level {j}: {cands.size} linear candidate(s), trying at most {ctx.cfg.maxLinear}"
  for c in cands.extract 0 ctx.cfg.maxLinear do
    match ← admit j c₀ "linear" c with
    | .admissible i k =>
      say s!"level {j}: linear template admitted: {c}"
      return some (c, i, k)
    | .noAnswer => return none
    | .rejected _ => pure ()
  return none

/-- The result of generalizing from the unsat cores: a clause, or `none` to fall back to
deletion. -/
def corePass (j : Nat) (c₀ : Clause) (rawI rawK : QueryResult) (iCore kCore : Option (Array Nat)) :
    SearchM (Option (Clause × QueryResult × QueryResult)) := do
  let cores := (← read).cfg.cores
  let (some kc, some ic) := (if cores then kCore else none, iCore)
    | say s!"level {j}: {if cores then "no unsat cores; falling back to deletion"
        else "deletion from the full diagram, cheapest literals first"}"
      return none
  let inCore (i : Nat) : Bool := kc.contains i || ic.contains i
  let kept := (Array.range c₀.lits.size).filter inCore
  if kept.isEmpty || kept.size == c₀.lits.size then
    let what := if kept.isEmpty then "are empty" else "cover every literal"
    say s!"level {j}: the unsat cores {what}; falling back to deletion"
    return none
  let c := c₀.restrict inCore
  match ← admit j c₀ "updr" c with
  | .admissible i k =>
    say s!"level {j}: core kept {c.lits.size} of {c₀.lits.size} literals"
    -- Minimizing a clause of one or two literals costs two calls per literal for little gain.
    if c.lits.size ≤ 2 then return some (c, i, k)
    return some (← minimize j c i k (admit j c₀ "updr"))
  | .noAnswer =>
    say s!"level {j}: no solver answer for the core-derived clause; keeping the raw clause"
    return some (c₀, rawI, rawK)
  | .rejected v =>
    say s!"level {j}: core-derived clause ({c.lits.size} literals) was \
      {Admission.describeRejection v}; falling back to deletion"
    return none

/-- Drop the literals of `c₀` one at a time, cheapest first, keeping each deletion that leaves the
clause admissible: at most forty tries with cores, every literal without. -/
def deletionPass (j : Nat) (c₀ : Clause) (rawI rawK : QueryResult) :
    SearchM (Clause × QueryResult × QueryResult) := do
  let order := (Array.range c₀.lits.size).qsort fun a b ↦
    literalRank c₀.lits[a]! < literalRank c₀.lits[b]!
  let maxTries := if (← read).cfg.cores then 40 else c₀.lits.size
  let mut keep := Array.replicate c₀.lits.size true
  let mut answers := (rawI, rawK)
  for idx in order.extract 0 maxTries do
    let keep' := keep.set! idx false
    let c := c₀.restrict (keep'[·]!)
    if c.lits.isEmpty then continue
    match ← admit j c₀ "updr" c with
    | .admissible i k => keep := keep'; answers := (i, k)
    | .noAnswer => break
    | .rejected _ => pure ()
  return (c₀.restrict (keep[·]!), answers)

/-- Generalize the blocking clause `c₀ = ¬ Diag(σ)` at level `j`. `rawI` and `rawK` are the
answers that admitted `c₀`, and `iCore` and `kCore` their unsat cores over its literals. -/
def generalize (j : Nat) (σ : FinStructure) (c₀ : Clause) (rawI rawK : QueryResult)
    (iCore kCore : Option (Array Nat)) : SearchM (Clause × QueryResult × QueryResult) := do
  let ctx ← read
  if !ctx.cfg.generalize then return (c₀, rawI, rawK)
  if ctx.cfg.generalizer == .linear && !ctx.sig.numericSorts.isEmpty then
    if let some r ← linearPass j σ c₀ then return r
  if let some r ← corePass j c₀ rawI rawK iCore kCore then return r
  deletionPass j c₀ rawI rawK

end SearchM

end Veil.Synthesizer
