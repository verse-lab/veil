module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Controller
public meta import Veil.Core.Tools.Synthesizer.Certificate
public meta import Veil.Core.Tools.Synthesizer.Counterexample

/-!
# `#synthesize_invariants`

This file defines the command, which runs UPDR on the current module's `safety` properties and
reports the outcome: strengthening clauses to paste into the module, a concrete counterexample, an
abstract counterexample showing that no universal inductive invariant exists, or why the search
stopped. With `certify`, an invariant or a counterexample becomes a kernel-checked theorem.

    #synthesize_invariants (fuel := 500) (log := "run.jsonl") (invariants := true) verbose certify

Options may appear in any order, each at most once.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil

register_option veil.synthesizer.timings : Bool := {
  defValue := false
  descr := "report separate wall times for IC3 synthesis and kernel certification"
}

syntax synthFuel := &"fuel" " := " num
syntax synthLog := &"log" " := " str
syntax synthExpectKind := &"invariant" <|> &"unsafe" <|> &"no_universal_invariant" <|> &"unknown"
syntax synthExpect := &"expect" " := " synthExpectKind
syntax synthInvariants := &"invariants" " := " (&"true" <|> &"false")
syntax synthGeneralizer := &"generalizer" " := " (&"updr" <|> &"linear")
syntax synthCores := &"cores" " := " (&"true" <|> &"false")
syntax synthOpt := "(" (synthFuel <|> synthLog <|> synthExpect <|> synthInvariants <|>
  synthGeneralizer <|> synthCores) ")"
/-- Search for universal invariants that make the module's `safety` properties inductive, with
UPDR. -/
syntax (name := synthesizeInvariants)
  "#synthesize_invariants" (synthOpt <|> &"verbose" <|> &"certify")* : command

/-- The outcome a test expects (`(expect := …)`). -/
inductive Expectation where
  | invariant | «unsafe» | noUniversalInvariant | unknown
deriving BEq, Repr

/-- An expectation in words. -/
def Expectation.describe : Expectation → String
  | .invariant => "an inductive invariant"
  | .«unsafe» => "a counterexample"
  | .noUniversalInvariant => "the no-universal-invariant verdict"
  | .unknown => "a stopped run"

/-- Whether an outcome is the one expected. -/
def Expectation.matches : Expectation → Outcome → Bool
  | .invariant, .foundInvariant .. => true
  | .«unsafe», .«unsafe» _ => true
  | .noUniversalInvariant, .noUniversalInvariant .. => true
  | .unknown, .unknown .. | .unknown, .absenceWithheld .. => true
  | _, _ => false

/-- An outcome in words. -/
def Outcome.describe : Outcome → String
  | .foundInvariant .. => "an inductive invariant"
  | .«unsafe» _ => "a counterexample"
  | .unsafeUndecoded .. => "a violation whose execution could not be decoded"
  | .noUniversalInvariant .. => "the no-universal-invariant verdict"
  | .unknown .. | .absenceWithheld .. => "a stopped run"
  | .internalError .. => "an internal error"

/-- The outcome as the log's `outcome` event reports it. -/
def Outcome.toJson : Outcome → Json
  | .foundInvariant frame clauses _ => Json.mkObj [("kind", "invariant"), ("frame", frame),
      ("clauses", Lean.toJson (clauses.map (clauseJson ·.clause)))]
  | .«unsafe» p => Json.mkObj [("kind", "unsafe"), ("steps", (p.states.size - 1 : Nat))]
  | .unsafeUndecoded k r => Json.mkObj [("kind", "unsafe"), ("steps", k), ("reason", r)]
  | .noUniversalInvariant ds _ =>
    Json.mkObj [("kind", "no_universal_invariant"), ("diagrams", ds.size)]
  | .absenceWithheld ds _ _ =>
    Json.mkObj [("kind", "unknown"), ("reason", absenceWithheldReason), ("diagrams", ds.size)]
  | .unknown r _ => Json.mkObj [("kind", "unknown"), ("reason", r)]
  | .internalError m _ => Json.mkObj [("kind", "internal_error"), ("message", m)]

/-- The options of a run of the command. -/
structure Options where
  cfg : Config := {}
  expectation : Option Expectation := none
  certify : Bool := false

/-- The word of a bare flag, which parses as an atom or a node around one. -/
def flag? : Syntax → Option String
  | .atom _ v | .node _ _ #[.atom _ v] => some v
  | _ => none

/-- Set one option; return its key and the new options. -/
def Options.set (opts : Options) (arg : Syntax) : CommandElabM (String × Options) := do
  let inner := if arg.isOfKind ``synthOpt then arg[1] else arg
  match flag? inner with
  | some "verbose" => return ("verbose", { opts with cfg.verbose := true })
  | some "certify" => return ("certify", { opts with certify := true })
  | some _ => throwErrorAt arg "unknown option"
  | none => pure ()
  match inner with
  | `(synthFuel| fuel := $n:num) => return ("fuel", { opts with cfg.fuel := n.getNat })
  | `(synthLog| log := $s:str) =>
    if s.getString.isEmpty then throwErrorAt s "the log file path is empty"
    return ("log", { opts with cfg.logFile := some (System.FilePath.mk s.getString) })
  | `(synthExpect| expect := invariant) =>
    return ("expect", { opts with expectation := some .invariant })
  | `(synthExpect| expect := unsafe) =>
    return ("expect", { opts with expectation := some .«unsafe» })
  | `(synthExpect| expect := no_universal_invariant) =>
    return ("expect", { opts with expectation := some .noUniversalInvariant })
  | `(synthExpect| expect := unknown) =>
    return ("expect", { opts with expectation := some .unknown })
  | `(synthInvariants| invariants := true) =>
    return ("invariants", { opts with cfg.useDeclaredInvariants := true })
  | `(synthInvariants| invariants := false) =>
    return ("invariants", { opts with cfg.useDeclaredInvariants := false })
  | `(synthGeneralizer| generalizer := updr) =>
    return ("generalizer", { opts with cfg.generalizer := .updr })
  | `(synthGeneralizer| generalizer := linear) =>
    return ("generalizer", { opts with cfg.generalizer := .linear })
  | `(synthCores| cores := true) => return ("cores", { opts with cfg.cores := true })
  | `(synthCores| cores := false) => return ("cores", { opts with cfg.cores := false })
  | _ => throwErrorAt arg "unknown option"

/-- Parse the options of the command; each may be given once. -/
def parseOptions (args : Array Syntax) : CommandElabM Options := do
  let mut opts : Options := {}
  let mut seen : Array String := #[]
  for arg in args do
    let (key, opts') ← opts.set arg
    if seen.contains key then throwErrorAt arg "the option {key} is given twice"
    seen := seen.push key
    opts := opts'
  return opts

/-! ### Messages -/

/-- Milliseconds as seconds, `s.d`. -/
def seconds (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- The strengthening clauses per frame. -/
def frameSummary (sizes : Array Nat) : String :=
  if sizes.isEmpty then "no frame opened"
  else
    s!"{sizes.size} frame(s) opened; strengthening clauses per frame F₁ … F_{sizes.size}: {sizes}"

/-- What the structures of an abstract counterexample are. -/
def chainDescription : String :=
  "the first is contained in an initial state, each next in a successor of a state containing the \
    previous, and a successor of a state containing the last violates the property"

/-- The structures of an abstract counterexample, one block each. -/
def renderChain (diagrams : Array FinStructure) : String :=
  "".intercalate (diagrams.toList.zipIdx.map fun (σ, i) ↦ s!"  structure {i + 1}:\n{σ.render}\n")

/-- What the axioms of a certificate say. -/
def certificateStatus (cert : CertificateResult) : String :=
  if cert.kernelChecked then "kernel-checked, standard axioms only"
  else
    let note := if cert.offenders.contains ``sorryAx then "; sorryAx means a solver step could \
      not be replayed as a Lean proof (lean-smt could not reconstruct it, or the kernel rejected \
      its reconstruction)" else ""
    s!"depends on {cert.offenders} beyond the standard axioms{note}"

/-- The report of the solver calls of a run. -/
def statsMessage (stats : RunStats) (status : TrNorm.Status) : String :=
  let ph := stats.phases
  let note := match status with
    | .normalized => s!"; transition relation normalized once in {seconds ph.normalizeMs} s"
    | .reused => "; transition relation reused from an earlier run in this module"
    | .failed => s!"; transition relation not normalized{if ph.normalizeMs > 0 then
        s!" ({seconds ph.normalizeMs} s spent on the attempt)" else ""}, the queries were written \
        with Veil's `tr`"
    | .off => "; transition relation not normalized (veil.synthesizer.normalizeTr false)"
    | .unused => ""
  s!"solver calls: {stats.solverCalls}, {seconds stats.solverMs} s (preprocessing \
    {seconds ph.preprocessMs} s, elaboration {seconds ph.elabMs} s, solving {seconds ph.smtMs} s, \
    decoding {seconds ph.decodeMs} s){note}"

/-- The report of an invariant. -/
def invariantMessage (frame : Nat) (clauses : Array Admitted) (anyTrusted trusting : Bool) :
    String :=
  let trustNote :=
    if !anyTrusted then " (lean-smt reconstructed every solver answer of the search as a proof \
      term; the search does not kernel-check those terms, `certify` does)"
    else if trusting then " (the search took the solver's answers on faith under \
      `veil.synthesizer.trust true`; a certificate reconstructs its own proofs)"
    else " (the search took some solver answers on faith because lean-smt could not replay their \
      proofs; a certificate reconstructs its own proofs and reports what it cannot)"
  if clauses.isEmpty then
    s!"Inductive invariant found at frame {frame}: the property is inductive on its own{trustNote}"
  else
    s!"Inductive invariant found at frame {frame} with {clauses.size} strengthening \
      clause(s){trustNote}:\n" ++
      "".intercalate (clauses.toList.zipIdx.map fun (a, k) ↦ s!"invariant [ic3_{k}] {a.clause}\n")

/-- The report of a no-universal-invariant verdict. -/
def absenceMessage (sig : Signature) (propertyName : String) (diagrams : Array FinStructure)
    (check : BoundedCheck) : String :=
  let ghostNote := if sig.ghosts.isEmpty then "" else
    s!"The ghost definitions {", ".intercalate (sig.ghosts.map toString).toList} are outside \
      that vocabulary: a clause over one of them unfolds to its body, and when the body has a \
      quantifier the clause is not universal, so this verdict says nothing about such clauses. "
  let excludedNote := if sig.excludedClassFields.isEmpty then "" else
    s!"The class fields {", ".intercalate (sig.excludedClassFields.map toString).toList} are \
      outside that vocabulary (their result type is outside the module's sorts), so this verdict \
      says nothing about clauses over them. "
  let basis := if sig.extendsPaper
    then "Proposition 5.6 of the paper, extended here to function symbols and enum sorts; see \
      docs/Synthesizer-Guide.md"
    else "Proposition 5.6 of the paper"
  let checkNote := match check with
    | .noAnswer k r => s!"The bounded path check of {k} step(s) got no answer ({r.take 160}), so \
        an execution of that length may violate the property.\n"
    | _ => ""
  s!"No universal inductive invariant over the module's vocabulary proves {propertyName}. \
    {ghostNote}{excludedNote}Abstract counterexample, {diagrams.size} structure(s): \
    {chainDescription} ({basis}).\n{renderChain diagrams}{checkNote}"

/-- The report of an abstract counterexample in a module with integer state. -/
def withheldMessage (diagrams : Array FinStructure) (check : BoundedCheck)
    (frameSizes : Array Nat) : String :=
  let checkNote := match check with
    | .notAsked => "The chain starts above the initial frame, so it describes no execution of the \
        frames' length. "
    | .noPath k => s!"No execution of {k} step(s) violates the property, so the chain is not a \
        real execution of that length. "
    | .noAnswer k r => s!"The bounded path check of {k} step(s) got no answer ({r.take 160}), so a \
        real execution of that length may exist. "
  s!"IC3 stopped: the search closed without an invariant. The no-universal-invariant verdict is \
    not given for a module with integer state (Proposition 5.6 of the paper is about uninterpreted \
    sorts), so this is not a verdict. {frameSummary frameSizes}. Abstract counterexample, \
    {diagrams.size} structure(s): {chainDescription}.\n{renderChain diagrams}{checkNote}The \
    property may need a strengthening outside the universal fragment (a Skolem ghost function \
    makes an existential fact universal; see \"Existential Invariants\" in \
    docs/Synthesizer-Guide.md), or it is false by a longer execution. Modeling the integer state \
    as an ordered sort makes the no-universal-invariant verdict available for the remodeled \
    module."

/-- The report of a stopped run, with a hint that follows the reason. -/
def stoppedMessage (reason : String) (frameSizes : Array Nat) : String :=
  let has (marker : String) : Bool := (reason.splitOn marker).length > 1
  let hint :=
    if has "fuel exhausted" then
      "Raise the budget with `(fuel := n)`. When the frontier frame keeps growing without clearing \
        (see the clause counts), the search is not converging and more budget will not help; \
        `(generalizer := updr)` or `(cores := false)` change which clauses are tried."
    else if reason.startsWith "frame limit" then
      "The frame limit is a constant of `Config`; a search that reaches it is unlikely to \
        converge, and the property may need an invariant outside the universal fragment."
    else if has "heartbeats" || has "exceeded its budget" then
      "The query overran the per-query heartbeat budget (a constant of `Solver.lean`), most often \
        in Veil's preprocessing of a large frame."
    else if has "failed:" then
      "A query could not be posed or its answer could not be read; this is a pipeline limitation, \
        not a solver budget."
    else if has solverUnknownPrefix then
      "The query was asked twice, the second time with twice `veil.smt.timeout`; raise that \
        option. Some modules produce queries outside the fragment cvc5 decides, and those run to \
        the timeout however large."
    else ""
  s!"IC3 stopped: {reason}. {frameSummary frameSizes}.{if hint.isEmpty then "" else " " ++ hint}"

/-- The report of a concrete counterexample, with a `sat trace` block that re-checks it. -/
def violationMessage (property : Array Term) (propertyName : String) (path : DecodedTrace) :
    CommandElabM String := do
  let actionOf : Json → String
    | .str s => s
    | .obj kvs => match kvs.toArray with
      | #[(k, _)] => k
      | _ => "any action"
    | _ => "any action"
  let mut msg := s!"Violated: {propertyName}. Execution of {path.states.size - 1} step(s):\n"
  for i in [:path.states.size] do
    msg := msg ++ s!"  state {i}:\n{path.states[i]!.render}\n"
    if i + 1 < path.states.size then msg := msg ++ s!"  step: {path.labels[i+1]!}\n"
  -- Each conjunct is wrapped in `uqc%` so that its capitals are quantified inside the negation.
  let props ← liftCoreM <| property.toList.mapM fun t ↦
    return s!"(uqc% ({← PrettyPrinter.ppTerm t}))"
  let stepLines := (path.labels.toList.drop 1).map fun l ↦ s!"    {actionOf l}\n"
  return msg ++ "Re-check with:\n  sat trace [ic3_cex] {\n" ++ "".intercalate stepLines ++
    s!"    assert ¬ ({" ∧ ".intercalate props})\n  }\n"

/-! ### The command -/

/-- Log a report as information when it is the expected outcome, at `severity` otherwise. -/
def logReport (expected : Bool) (severity : MessageSeverity) (msg : String) :
    CommandElabM Unit := do
  logAt (← getRef) msg (if expected then .information else severity)

/-- Report the wall time of a phase under `veil.synthesizer.timings`. -/
def reportPhaseTime (phase : String) (started : Nat) : CommandElabM Unit := do
  if veil.synthesizer.timings.get (← getOptions) then
    logInfo s!"IC3 timing {phase}: {(← IO.monoMsNow) - started} ms"

@[command_elab synthesizeInvariants]
def elabSynthesizeInvariants : CommandElab := fun stx ↦ do
  let mod ← getCurrentModule (errMsg := "#synthesize_invariants must be used inside a Veil module")
  mod.throwIfSpecNotFinalized
  let { cfg, expectation, certify := doCertify } ← parseOptions stx[1].getArgs
  -- Refuse an unsupported module, a module without a property and a bad fault hook before running.
  let sig ← liftTermElabM (Signature.ofModule mod)
  let property ← liftCoreM (checkedProperty mod cfg)
  let _ ← liftCoreM TrNorm.faultPoint
  let _ ← liftCoreM failQueryAt
  let propertyName :=
    if mod.safeties.isEmpty then "the declared invariants"
    else if cfg.useDeclaredInvariants then
      "the safety property together with the declared invariants"
    else "the safety property"
  -- The transition system does not assume trusted invariants.
  let trustedNote :=
    if mod.trustedInvariants.isEmpty then "" else " (trusted invariants were not assumed)"
  if doCertify then throwIfCertified mod [`ic3_prop, `ic3_safe, `ic3_unsafe, `ic3_init_0]
  liftCoreM (TrNorm.throwIfForeign mod)
  let trNormBefore := (← liftCoreM (TrNorm.available mod)).isSome
  let unassigned := Signature.unassignedByInit mod
  unless unassigned.isEmpty do
    logWarning s!"IC3: after_init does not assign \
      {", ".intercalate (unassigned.map toString).toList}; the certificate's initial states keep \
      the default value of these components, and #check_invariants may reject a clause that \
      relies on it (see \"Semantics\" in docs/Synthesizer-Guide.md)"
  let started ← IO.monoMsNow
  let { outcome, stats, .. } ← liftTermElabM <| synthesize mod cfg sig
  reportPhaseTime "synthesis" started
  let status ← liftCoreM (TrNorm.status mod trNormBefore)
  logInfo (statsMessage stats status)
  if let some path := cfg.logFile then
    let ph := stats.phases
    try
      appendEvent path <| Json.mkObj [("event", "outcome"), ("module", toString mod.name),
        ("solverCalls", stats.solverCalls), ("solverMs", stats.solverMs),
        ("preprocessMs", ph.preprocessMs), ("elabMs", ph.elabMs), ("smtMs", ph.smtMs),
        ("decodeMs", ph.decodeMs), ("normalizeMs", ph.normalizeMs), ("trNorm", status.key),
        ("outcome", outcome.toJson)]
    catch e =>
      logWarning m!"IC3: could not append the outcome to the log file {path}: {e.toMessageData}"
  let expected := expectation.any (·.matches outcome)
  if let some e := expectation then
    unless expected do logError s!"expected {e.describe}, got {outcome.describe}"
  let certifyTimed (x : CommandElabM CertificateResult) : CommandElabM CertificateResult := do
    let started ← IO.monoMsNow
    let cert ← x
    reportPhaseTime "certification" started
    return cert
  match outcome with
  | .foundInvariant frame clauses anyTrusted =>
    logInfo (invariantMessage frame clauses anyTrusted (veil.synthesizer.trust.get (← getOptions)))
    if doCertify then
      let cert ← certifyTimed <| certify mod property (clauses.map (·.clause))
      logInfo s!"Certified: theorem {cert.theoremName} (strengthening {cert.strengtheningName}); \
        axioms: {cert.axioms}; {certificateStatus cert}"
  | .«unsafe» path =>
    logReport expected .error (← violationMessage property (propertyName ++ trustedNote) path)
    if doCertify then
      let cert ← certifyTimed <| certifyUnsafe mod property path
      logInfo s!"Certified: theorem {cert.theoremName} refutes {propertyName} at the model's sort \
        sizes and typeclass instances; axioms: {cert.axioms}; {certificateStatus cert}"
  | .unsafeUndecoded steps reason =>
    logError s!"Violated: {propertyName}{trustedNote}. The solver found an execution of {steps} \
      step(s) that breaks it, but its model could not be decoded ({reason.take 300}), so the \
      execution is not shown{if doCertify then "; no certificate is built" else ""}."
  | .noUniversalInvariant diagrams check =>
    logReport expected .warning (absenceMessage sig (propertyName ++ trustedNote) diagrams check)
  | .absenceWithheld diagrams check frameSizes =>
    logReport expected .warning (withheldMessage diagrams check frameSizes)
  | .unknown reason frameSizes => logReport expected .warning (stoppedMessage reason frameSizes)
  | .internalError message frameSizes =>
    logError s!"IC3 internal error: {message}. {frameSummary frameSizes}. This is a bug in the \
      controller or in the model decoder, not a solver limit."

end Veil.Synthesizer
