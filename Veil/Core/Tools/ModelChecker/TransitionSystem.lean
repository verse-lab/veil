import Veil.Core.Tools.ModelChecker.ExecutionOutcome

namespace Veil

structure TransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) where

/-- A relational transition system is parametrised by:
  - `ρ` - the type of the background theory (immutable state) it operates in
  - `σ` - the type of the state it operates on
  - `l` - the type of the transition labels (including the names of the
  transitions and the parameters they take)
  - `assumptions` - the set of acceptable background theories
  - `init` - the set of initial states, indexed by background theory they
  operate in
  - `tr` - the transition relation

A relational transition system might or might be executable, depending on
whether `assumptions`, `init`, and `tr` are decidable.
-/
@[grind]
structure RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends TransitionSystem ρ σ l where
  /-- The set of acceptable background theories -/
  assumptions : ρ → Prop
  /-- The set of initial states, indexed by background theory -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  tr : ρ → σ → l → σ → Prop

attribute [grind] RelationalTransitionSystem.assumptions RelationalTransitionSystem.init RelationalTransitionSystem.tr

structure LawfulRelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends RelationalTransitionSystem ρ σ l where
  /-- The initial states satisfy the assumptions -/
  initSatisfiesAssumptions : ∀ (th : ρ) (s : σ), init th s → assumptions th

namespace RelationalTransitionSystem

/-- A version of the transition relation that "hides" which particular
transition was taken. -/
@[grind]
def next (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s s' : σ) : Prop :=
  ∃ label, sys.tr th s label s'

/-- Reachability relation, indexed by background theory -/
@[grind cases, grind intro]
inductive reachable (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions th → sys.init th s → sys.reachable th s
  | step : ∀ (s s' : σ), sys.reachable th s → sys.next th s s' → sys.reachable th s'

/-- A finite labeled execution fragment. -/
@[grind cases, grind intro]
inductive multistep (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → List l → σ → Prop where
  | refl : ∀ {s : σ}, sys.multistep th s [] s
  | stepL : ∀ {s s' s'' : σ} {label : l} {labels : List l},
      sys.tr th s label s' → sys.multistep th s' labels s'' →
      sys.multistep th s (label :: labels) s''

/-- A finite execution fragment that hides the labels taken. -/
@[grind]
def canReach (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s s' : σ) : Prop :=
  ∃ labels, sys.multistep th s labels s'

/-- A state predicate holds for every state reachable under every admissible
background theory. -/
@[grind]
def isInvariant (sys : RelationalTransitionSystem ρ σ l) (p : ρ → σ → Prop) : Prop :=
  ∀ th st, sys.reachable th st → p th st

namespace multistep

/-- A single transition is a one-step execution fragment. -/
@[grind .]
theorem single {sys : RelationalTransitionSystem ρ σ l} {th : ρ} {s s' : σ} {label : l}
    (h : sys.tr th s label s') :
    sys.multistep th s [label] s' := by
  exact multistep.stepL h multistep.refl

/-- Finite execution fragments compose by concatenating labels. -/
@[grind .]
theorem comp {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    {s₁ s₂ s₃ : σ} {labels₁ labels₂ : List l}
    (h₁ : sys.multistep th s₁ labels₁ s₂)
    (h₂ : sys.multistep th s₂ labels₂ s₃) :
    sys.multistep th s₁ (labels₁ ++ labels₂) s₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | stepL htr hm ih =>
      exact multistep.stepL htr (ih h₂)

end multistep

namespace canReach

@[grind .]
theorem refl (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s : σ) :
    sys.canReach th s s := by
  exact ⟨[], multistep.refl⟩

@[grind .]
theorem single {sys : RelationalTransitionSystem ρ σ l} {th : ρ} {s s' : σ}
    (h : sys.next th s s') :
    sys.canReach th s s' := by
  rcases h with ⟨label, htr⟩
  exact ⟨[label], multistep.single htr⟩

@[grind .]
theorem single_tr {sys : RelationalTransitionSystem ρ σ l} {th : ρ} {s s' : σ} {label : l}
    (h : sys.tr th s label s') :
    sys.canReach th s s' := by
  exact ⟨[label], multistep.single h⟩

@[grind .]
theorem comp {sys : RelationalTransitionSystem ρ σ l} {th : ρ} {s₁ s₂ s₃ : σ}
    (h₁ : sys.canReach th s₁ s₂) (h₂ : sys.canReach th s₂ s₃) :
    sys.canReach th s₁ s₃ := by
  rcases h₁ with ⟨labels₁, hm₁⟩
  rcases h₂ with ⟨labels₂, hm₂⟩
  exact ⟨labels₁ ++ labels₂, multistep.comp hm₁ hm₂⟩

end canReach

/-- A relation lifting one-step label matching to finite traces. Each concrete
label is matched by one abstract label trace, and the abstract traces are
concatenated in order. -/
@[grind cases, grind intro]
inductive TraceMatch (matchLabel : lc → List la → Prop) : List lc → List la → Prop where
  | nil : TraceMatch matchLabel [] []
  | cons : ∀ {label : lc} {labels : List lc} {abstractLabels abstractLabels' : List la},
      matchLabel label abstractLabels →
      TraceMatch matchLabel labels abstractLabels' →
      TraceMatch matchLabel (label :: labels) (abstractLabels ++ abstractLabels')

namespace TraceMatch

/-- Identity trace matching through singleton label traces. -/
@[grind .]
theorem singleton (labels : List l) :
    TraceMatch (fun label abstractLabels => abstractLabels = [label]) labels labels := by
  induction labels with
  | nil => exact TraceMatch.nil
  | cons label labels ih =>
      simpa using TraceMatch.cons (label := label) (labels := labels)
        (abstractLabels := [label]) (abstractLabels' := labels) rfl ih

/-- Trace matching composes by matching the intermediate trace pointwise. -/
@[grind .]
theorem split_append
    {matchLabel : lm → List la → Prop}
    {labels₁ labels₂ : List lm} {abstractLabels : List la}
    (h : TraceMatch matchLabel (labels₁ ++ labels₂) abstractLabels) :
    ∃ abstractLabels₁ abstractLabels₂,
      abstractLabels = abstractLabels₁ ++ abstractLabels₂ ∧
      TraceMatch matchLabel labels₁ abstractLabels₁ ∧
      TraceMatch matchLabel labels₂ abstractLabels₂ := by
  induction labels₁ generalizing abstractLabels with
  | nil =>
      exact ⟨[], abstractLabels, by simp, TraceMatch.nil, by simpa using h⟩
  | cons label labels₁ ih =>
      cases h with
      | cons hlabel htail =>
          rcases ih htail with ⟨abstractLabels₁, abstractLabels₂, heq, h₁, h₂⟩
          refine ⟨_, abstractLabels₂, ?_, TraceMatch.cons hlabel h₁, h₂⟩
          simp [heq, List.append_assoc]

/-- Trace matching composes by matching the intermediate trace pointwise. -/
@[grind .]
theorem comp
    {match₁ : lc → List lm → Prop} {match₂ : lm → List la → Prop}
    {concreteLabels : List lc} {middleLabels : List lm} {abstractLabels : List la}
    (h₁ : TraceMatch match₁ concreteLabels middleLabels)
    (h₂ : TraceMatch match₂ middleLabels abstractLabels) :
    TraceMatch
      (fun concreteLabel abstractLabels =>
        ∃ middleLabels, match₁ concreteLabel middleLabels ∧
          TraceMatch match₂ middleLabels abstractLabels)
      concreteLabels abstractLabels := by
  induction h₁ generalizing abstractLabels with
  | nil =>
      cases h₂
      exact TraceMatch.nil
  | cons hlabel hlabels ih =>
      rename_i label labels middleLabels₁ middleLabels₂
      rcases split_append h₂ with
        ⟨abstractLabels₁, abstractLabels₂, heq, hmatch₁, hmatch₂⟩
      subst abstractLabels
      exact TraceMatch.cons ⟨middleLabels₁, hlabel, hmatch₁⟩ (ih hmatch₂)

end TraceMatch

/-- Assumptions hold in all reachable states. -/
@[grind .]
theorem reachable_assumptions (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s : σ) (h : reachable sys th s) : sys.assumptions th := by
  induction h with
  | init s has hinit => assumption
  | step s s' h2 hn ih => assumption

/-- Reachability is preserved under inclusion of transition systems. -/
@[grind .]
theorem reachable_inclusion (sys : RelationalTransitionSystem ρ σ l) (sys' : RelationalTransitionSystem ρ σ l)
  (hass_implies : ∀ (r : ρ), sys.assumptions r → sys'.assumptions r)
  (hinit_implies : ∀ (r : ρ) (st : σ), sys.init r st → sys'.init r st)
  (hnext_implies : ∀ (r : ρ) (st st' : σ), sys.next r st st' → sys'.next r st st') :
  ∀ (r : ρ) (st : σ), sys.reachable r st → sys'.reachable r st := by
  intro r st h
  induction h with
  | init s has hinit => apply reachable.init _ (hass_implies r has) (hinit_implies r s hinit)
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

/-- Reachability is closed under finite transition fragments. -/
@[grind .]
theorem reachable_of_canReach (sys : RelationalTransitionSystem ρ σ l) {th : ρ} {s s' : σ}
    (hreach : sys.reachable th s) (hsteps : sys.canReach th s s') :
    sys.reachable th s' := by
  rcases hsteps with ⟨labels, hm⟩
  induction hm with
  | refl => exact hreach
  | stepL htr _ ih =>
      exact ih (reachable.step _ _ hreach ⟨_, htr⟩)

/-- Forward simulation between two transition systems, allowing different
background theory, state, and label types. Each concrete step may be matched by
zero or more abstract steps. -/
structure ForwardSimulation
    (concrete : RelationalTransitionSystem ρc σc lc)
    (abstract : RelationalTransitionSystem ρa σa la)
    (mapTheory : ρc → ρa)
    (rel : ρc → σc → σa → Prop) : Prop where
  assumptions : ∀ th, concrete.assumptions th → abstract.assumptions (mapTheory th)
  init : ∀ th sc, concrete.assumptions th → concrete.init th sc →
    ∃ sa, abstract.init (mapTheory th) sa ∧ rel th sc sa
  step : ∀ th sc sc' sa label, concrete.assumptions th → rel th sc sa →
    concrete.tr th sc label sc' →
    ∃ sa', abstract.canReach (mapTheory th) sa sa' ∧ rel th sc' sa'

namespace ForwardSimulation

theorem reachable
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    (sim : ForwardSimulation concrete abstract mapTheory rel)
    {th : ρc} {sc : σc} :
    concrete.reachable th sc →
    ∃ sa, abstract.reachable (mapTheory th) sa ∧ rel th sc sa := by
  intro hreach
  induction hreach with
  | init sc hass hinit =>
      rcases sim.init th sc hass hinit with ⟨sa, hinitA, hrel⟩
      exact ⟨sa, RelationalTransitionSystem.reachable.init sa (sim.assumptions th hass) hinitA, hrel⟩
  | step sc sc' hreach hnext ih =>
      rcases ih with ⟨sa, hreachA, hrel⟩
      rcases hnext with ⟨label, htr⟩
      have hass := concrete.reachable_assumptions th sc hreach
      rcases sim.step th sc sc' sa label hass hrel htr with ⟨sa', hsteps, hrel'⟩
      exact ⟨sa', abstract.reachable_of_canReach hreachA hsteps, hrel'⟩

theorem invariant
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    (sim : ForwardSimulation concrete abstract mapTheory rel)
    {pConcrete : ρc → σc → Prop} {pAbstract : ρa → σa → Prop}
    (habs : abstract.isInvariant pAbstract)
    (hrel : ∀ th sc sa, rel th sc sa → pAbstract (mapTheory th) sa → pConcrete th sc) :
    concrete.isInvariant pConcrete := by
  intro th sc hreach
  rcases sim.reachable hreach with ⟨sa, hreachA, hsrel⟩
  exact hrel th sc sa hsrel (habs (mapTheory th) sa hreachA)

end ForwardSimulation

/-- A fixed-theory forward simulation. This is useful when the abstract state
type or theory is chosen after fixing one concrete background theory. -/
structure PointedForwardSimulation
    (concrete : RelationalTransitionSystem ρc σc lc)
    (abstract : RelationalTransitionSystem ρa σa la)
    (thConcrete : ρc) (thAbstract : ρa)
    (rel : σc → σa → Prop) : Prop where
  assumptions : concrete.assumptions thConcrete → abstract.assumptions thAbstract
  init : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
    ∃ sa, abstract.init thAbstract sa ∧ rel sc sa
  step : ∀ sc sc' sa label, concrete.assumptions thConcrete → rel sc sa →
    concrete.tr thConcrete sc label sc' →
    ∃ sa', abstract.canReach thAbstract sa sa' ∧ rel sc' sa'

namespace PointedForwardSimulation

theorem reachable
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    (sim : PointedForwardSimulation concrete abstract thConcrete thAbstract rel)
    {sc : σc} :
    concrete.reachable thConcrete sc →
    ∃ sa, abstract.reachable thAbstract sa ∧ rel sc sa := by
  intro hreach
  induction hreach with
  | init sc hass hinit =>
      rcases sim.init sc hass hinit with ⟨sa, hinitA, hrel⟩
      exact ⟨sa, RelationalTransitionSystem.reachable.init sa (sim.assumptions hass) hinitA, hrel⟩
  | step sc sc' hreach hnext ih =>
      rcases ih with ⟨sa, hreachA, hrel⟩
      rcases hnext with ⟨label, htr⟩
      have hass := concrete.reachable_assumptions thConcrete sc hreach
      rcases sim.step sc sc' sa label hass hrel htr with ⟨sa', hsteps, hrel'⟩
      exact ⟨sa', abstract.reachable_of_canReach hreachA hsteps, hrel'⟩

theorem invariant
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    (sim : PointedForwardSimulation concrete abstract thConcrete thAbstract rel)
    {pConcrete : σc → Prop} {pAbstract : σa → Prop}
    (habs : ∀ sa, abstract.reachable thAbstract sa → pAbstract sa)
    (hrel : ∀ sc sa, rel sc sa → pAbstract sa → pConcrete sc) :
    ∀ sc, concrete.reachable thConcrete sc → pConcrete sc := by
  intro sc hreach
  rcases sim.reachable hreach with ⟨sa, hreachA, hsrel⟩
  exact hrel sc sa hsrel (habs sa hreachA)

end PointedForwardSimulation

/-- Trace-aware forward simulation between two transition systems. Each
concrete step is matched by a finite abstract execution whose label trace is
related to the concrete label. -/
structure TraceForwardSimulation
    (concrete : RelationalTransitionSystem ρc σc lc)
    (abstract : RelationalTransitionSystem ρa σa la)
    (mapTheory : ρc → ρa)
    (rel : ρc → σc → σa → Prop)
    (matchLabel : lc → List la → Prop) : Prop where
  assumptions : ∀ th, concrete.assumptions th → abstract.assumptions (mapTheory th)
  init : ∀ th sc, concrete.assumptions th → concrete.init th sc →
    ∃ sa, abstract.init (mapTheory th) sa ∧ rel th sc sa
  step : ∀ th sc sc' sa label, concrete.assumptions th → rel th sc sa →
    concrete.tr th sc label sc' →
    ∃ labels sa',
      matchLabel label labels ∧
      abstract.multistep (mapTheory th) sa labels sa' ∧
      rel th sc' sa'

namespace TraceForwardSimulation

/-- Erase trace information from a trace-aware simulation. -/
@[grind .]
theorem toForwardSimulation
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : TraceForwardSimulation concrete abstract mapTheory rel matchLabel) :
    ForwardSimulation concrete abstract mapTheory rel where
  assumptions := sim.assumptions
  init := sim.init
  step := by
    intro th sc sc' sa label hass hrel htr
    rcases sim.step th sc sc' sa label hass hrel htr with
      ⟨labels, sa', _hmatch, hsteps, hrel'⟩
    exact ⟨sa', ⟨labels, hsteps⟩, hrel'⟩

/-- Reachability is transported by a trace-aware simulation. -/
@[grind .]
theorem reachable
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : TraceForwardSimulation concrete abstract mapTheory rel matchLabel)
    {th : ρc} {sc : σc} :
    concrete.reachable th sc →
    ∃ sa, abstract.reachable (mapTheory th) sa ∧ rel th sc sa :=
  sim.toForwardSimulation.reachable

/-- Concrete finite executions lift to abstract finite executions with
matching traces. -/
theorem multistep
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : TraceForwardSimulation concrete abstract mapTheory rel matchLabel)
    {th : ρc} {sc sc' : σc} {labels : List lc} {sa : σa}
    (hass : concrete.assumptions th) (hrel : rel th sc sa)
    (hsteps : concrete.multistep th sc labels sc') :
    ∃ abstractLabels sa',
      TraceMatch matchLabel labels abstractLabels ∧
      abstract.multistep (mapTheory th) sa abstractLabels sa' ∧
      rel th sc' sa' := by
  induction hsteps generalizing sa with
  | refl =>
      exact ⟨[], sa, TraceMatch.nil, multistep.refl, hrel⟩
  | stepL htr hrest ih =>
      rcases sim.step th _ _ sa _ hass hrel htr with
        ⟨abstractLabels₁, sa₁, hmatch₁, hsteps₁, hrel₁⟩
      rcases ih hrel₁ with
        ⟨abstractLabels₂, sa₂, hmatch₂, hsteps₂, hrel₂⟩
      exact ⟨abstractLabels₁ ++ abstractLabels₂, sa₂,
        TraceMatch.cons hmatch₁ hmatch₂,
        multistep.comp hsteps₁ hsteps₂,
        hrel₂⟩

/-- Initialized concrete finite executions are included in initialized
abstract finite executions modulo trace matching. -/
@[grind .]
theorem init_multistep
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory : ρc → ρa} {rel : ρc → σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : TraceForwardSimulation concrete abstract mapTheory rel matchLabel)
    {th : ρc} {sc sc' : σc} {labels : List lc}
    (hass : concrete.assumptions th) (hinit : concrete.init th sc)
    (hsteps : concrete.multistep th sc labels sc') :
    ∃ sa sa' abstractLabels,
      abstract.init (mapTheory th) sa ∧
      rel th sc sa ∧
      TraceMatch matchLabel labels abstractLabels ∧
      abstract.multistep (mapTheory th) sa abstractLabels sa' ∧
      rel th sc' sa' := by
  rcases sim.init th sc hass hinit with ⟨sa, hinitA, hrel⟩
  rcases sim.multistep hass hrel hsteps with
    ⟨abstractLabels, sa', hmatch, hstepsA, hrel'⟩
  exact ⟨sa, sa', abstractLabels, hinitA, hrel, hmatch, hstepsA, hrel'⟩

/-- Reflexive trace simulation using singleton label traces. -/
@[grind .]
theorem refl (sys : RelationalTransitionSystem ρ σ l) :
    TraceForwardSimulation sys sys id
      (fun _ s s' => s = s')
      (fun label labels => labels = [label]) where
  assumptions := by intro _ h; exact h
  init := by
    intro th sc _ hinit
    exact ⟨sc, hinit, rfl⟩
  step := by
    intro th sc sc' sa label _ hrel htr
    subst sa
    exact ⟨[label], sc', rfl, multistep.single htr, rfl⟩

/-- Trace simulations compose. -/
@[grind .]
theorem comp
    {concrete : RelationalTransitionSystem ρc σc lc}
    {middle : RelationalTransitionSystem ρm σm lm}
    {abstract : RelationalTransitionSystem ρa σa la}
    {mapTheory₁ : ρc → ρm} {mapTheory₂ : ρm → ρa}
    {rel₁ : ρc → σc → σm → Prop} {rel₂ : ρm → σm → σa → Prop}
    {match₁ : lc → List lm → Prop} {match₂ : lm → List la → Prop}
    (sim₁ : TraceForwardSimulation concrete middle mapTheory₁ rel₁ match₁)
    (sim₂ : TraceForwardSimulation middle abstract mapTheory₂ rel₂ match₂) :
    TraceForwardSimulation concrete abstract (fun th => mapTheory₂ (mapTheory₁ th))
      (fun th sc sa => ∃ sm, rel₁ th sc sm ∧ rel₂ (mapTheory₁ th) sm sa)
      (fun label abstractLabels =>
        ∃ middleLabels, match₁ label middleLabels ∧ TraceMatch match₂ middleLabels abstractLabels) where
  assumptions := by
    intro th hass
    exact sim₂.assumptions (mapTheory₁ th) (sim₁.assumptions th hass)
  init := by
    intro th sc hass hinit
    rcases sim₁.init th sc hass hinit with ⟨sm, hinitM, hrel₁⟩
    rcases sim₂.init (mapTheory₁ th) sm (sim₁.assumptions th hass) hinitM with
      ⟨sa, hinitA, hrel₂⟩
    exact ⟨sa, hinitA, sm, hrel₁, hrel₂⟩
  step := by
    intro th sc sc' sa label hass hrel htr
    rcases hrel with ⟨sm, hrel₁, hrel₂⟩
    rcases sim₁.step th sc sc' sm label hass hrel₁ htr with
      ⟨middleLabels, sm', hmatch₁, hstepsM, hrel₁'⟩
    rcases sim₂.multistep (sim₁.assumptions th hass) hrel₂ hstepsM with
      ⟨abstractLabels, sa', hmatch₂, hstepsA, hrel₂'⟩
    exact ⟨abstractLabels, sa',
      ⟨middleLabels, hmatch₁, hmatch₂⟩,
      hstepsA,
      ⟨sm', hrel₁', hrel₂'⟩⟩

end TraceForwardSimulation

/-- A fixed-theory trace-aware forward simulation. -/
structure PointedTraceForwardSimulation
    (concrete : RelationalTransitionSystem ρc σc lc)
    (abstract : RelationalTransitionSystem ρa σa la)
    (thConcrete : ρc) (thAbstract : ρa)
    (rel : σc → σa → Prop)
    (matchLabel : lc → List la → Prop) : Prop where
  assumptions : concrete.assumptions thConcrete → abstract.assumptions thAbstract
  init : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
    ∃ sa, abstract.init thAbstract sa ∧ rel sc sa
  step : ∀ sc sc' sa label, concrete.assumptions thConcrete → rel sc sa →
    concrete.tr thConcrete sc label sc' →
    ∃ labels sa',
      matchLabel label labels ∧
      abstract.multistep thAbstract sa labels sa' ∧
      rel sc' sa'

namespace PointedTraceForwardSimulation

/-- Erase trace information from a pointed trace-aware simulation. -/
@[grind .]
theorem toPointedForwardSimulation
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : PointedTraceForwardSimulation concrete abstract thConcrete thAbstract rel matchLabel) :
    PointedForwardSimulation concrete abstract thConcrete thAbstract rel where
  assumptions := sim.assumptions
  init := sim.init
  step := by
    intro sc sc' sa label hass hrel htr
    rcases sim.step sc sc' sa label hass hrel htr with
      ⟨labels, sa', _hmatch, hsteps, hrel'⟩
    exact ⟨sa', ⟨labels, hsteps⟩, hrel'⟩

/-- Reachability is transported by a pointed trace-aware simulation. -/
@[grind .]
theorem reachable
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : PointedTraceForwardSimulation concrete abstract thConcrete thAbstract rel matchLabel)
    {sc : σc} :
    concrete.reachable thConcrete sc →
    ∃ sa, abstract.reachable thAbstract sa ∧ rel sc sa :=
  sim.toPointedForwardSimulation.reachable

/-- Concrete finite executions lift to abstract finite executions with
matching traces. -/
theorem multistep
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : PointedTraceForwardSimulation concrete abstract thConcrete thAbstract rel matchLabel)
    {sc sc' : σc} {labels : List lc} {sa : σa}
    (hass : concrete.assumptions thConcrete) (hrel : rel sc sa)
    (hsteps : concrete.multistep thConcrete sc labels sc') :
    ∃ abstractLabels sa',
      TraceMatch matchLabel labels abstractLabels ∧
      abstract.multistep thAbstract sa abstractLabels sa' ∧
      rel sc' sa' := by
  induction hsteps generalizing sa with
  | refl =>
      exact ⟨[], sa, TraceMatch.nil, multistep.refl, hrel⟩
  | stepL htr hrest ih =>
      rcases sim.step _ _ sa _ hass hrel htr with
        ⟨abstractLabels₁, sa₁, hmatch₁, hsteps₁, hrel₁⟩
      rcases ih hrel₁ with
        ⟨abstractLabels₂, sa₂, hmatch₂, hsteps₂, hrel₂⟩
      exact ⟨abstractLabels₁ ++ abstractLabels₂, sa₂,
        TraceMatch.cons hmatch₁ hmatch₂,
        multistep.comp hsteps₁ hsteps₂,
        hrel₂⟩

/-- Initialized concrete finite executions are included in initialized
abstract finite executions modulo trace matching. -/
@[grind .]
theorem init_multistep
    {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    {matchLabel : lc → List la → Prop}
    (sim : PointedTraceForwardSimulation concrete abstract thConcrete thAbstract rel matchLabel)
    {sc sc' : σc} {labels : List lc}
    (hass : concrete.assumptions thConcrete) (hinit : concrete.init thConcrete sc)
    (hsteps : concrete.multistep thConcrete sc labels sc') :
    ∃ sa sa' abstractLabels,
      abstract.init thAbstract sa ∧
      rel sc sa ∧
      TraceMatch matchLabel labels abstractLabels ∧
      abstract.multistep thAbstract sa abstractLabels sa' ∧
      rel sc' sa' := by
  rcases sim.init sc hass hinit with ⟨sa, hinitA, hrel⟩
  rcases sim.multistep hass hrel hsteps with
    ⟨abstractLabels, sa', hmatch, hstepsA, hrel'⟩
  exact ⟨sa, sa', abstractLabels, hinitA, hrel, hmatch, hstepsA, hrel'⟩

end PointedTraceForwardSimulation

end RelationalTransitionSystem

/-- An enumerable transition system that tracks execution outcomes including
assertion failures. The `tr` function returns a set of labeled outcomes,
where each outcome can be a successful transition, an assertion failure,
or divergence.

Parameters:
- `ρ` - the type of the background theory (immutable state)
- `σ` - the type of the mutable state
- `ε` - the type of exceptions/assertion failure identifiers
- `l` - the type of transition labels
- `th` - the specific background theory this system operates under -/
structure EnumerableTransitionSystem
  (ρ : Type) (ρSet : outParam Type) [Std.Stream ρSet ρ]
  (σ : Type) (σSet : outParam Type) [Std.Stream σSet σ]
  (ε : Type)
  (l : outParam Type)
  (outcomeSet : Type) [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  (th : ρ)
  extends TransitionSystem ρ σ l where
  /-- The (enumerable) set of initial states -/
  initStates : σSet
  /-- The (enumerable) set of transition labels and execution outcomes.
  Each outcome may be a successful post-state, an assertion failure, or divergence. -/
  tr : ρ → σ → outcomeSet

attribute [grind] EnumerableTransitionSystem.initStates EnumerableTransitionSystem.tr

namespace EnumerableTransitionSystem

/-- Extract only successful transitions (ignoring assertion failures and divergence). -/
@[grind]
def next
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th) (s s' : σ) : Prop :=
  ∃ label, (label, ExecutionOutcome.success s') ∈ sys.tr th s

@[grind]
def toRelational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th) :
  RelationalTransitionSystem ρ σ l
where
  assumptions := fun th' => th' = th
  init := fun _ st => st ∈ sys.initStates
  tr := fun th st label st' => (label, ExecutionOutcome.success st') ∈ sys.tr th st


/-- Reachability relation, indexed by background theory.
Only considers successful transitions (assertion failures don't lead to new reachable states). -/
@[grind]
inductive reachable
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th)
  : σ → Prop
where
  | init : ∀ (s : σ), s ∈ sys.initStates → sys.reachable s
  | step : ∀ (s s' : σ), sys.reachable s → sys.next s s' → sys.reachable s'

theorem reachable_equiv_relational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th)
  :
  sys.reachable s ↔ (sys.toRelational.reachable th s) := by
  constructor
  · intro h
    induction h with
    | init s hinit =>
      exact RelationalTransitionSystem.reachable.init s rfl hinit
    | step s s' _ hnext ih =>
      exact RelationalTransitionSystem.reachable.step s s' ih hnext
  · intro h
    induction h with
    | init s _ hinit =>
      exact reachable.init s hinit
    | step s s' _ hnext ih =>
      exact reachable.step s s' ih hnext

end EnumerableTransitionSystem

end Veil
