module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/DiningPhilosophers/DiningPhilosophersPCal.tla
-- Chandy-Misra dining philosophers (PlusCal); the translated `Spec`, with `NP = 5`.

veil module DiningPhilosophers

type philosopher

-- Used purely to allow syntax close to TLA+ on an abstract type, with parametric NP
immutable function succ : philosopher → philosopher -- p+1 on 1..NP, wrapping NP ↦ 1
immutable function pred : philosopher → philosopher -- p-1 on 1..NP, wrapping 1 ↦ NP
immutable function ph : Nat → philosopher           -- the philosopher (fork) numbered k

-- Actions are `_`-prefixed: a bare `Loop` action would shadow this enum's `Loop`.
enum pcLabel = { Loop, Eat, Think }

-- [holder: 1..NP, clean: BOOLEAN]
@[veil_decl] structure Fork (philosopher : Type) where
  holder : philosopher
  clean : Bool

-- VARIABLES forks, pc, hungry
function forks : philosopher → Fork philosopher
function pc : philosopher → pcLabel
relation hungry : philosopher → Bool

#gen_state

-- LeftFork(p) == p
ghost function LeftFork (p : philosopher) := p
-- RightFork(p) == IF p = NP THEN 1 ELSE p + 1
ghost function RightFork (p : philosopher) := succ p
-- LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
ghost function LeftPhilosopher (p : philosopher) := pred p
-- RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1
ghost function RightPhilosopher (p : philosopher) := succ p

-- IsHoldingBothForks(p) == forks[LeftFork(p)].holder = p /\ forks[RightFork(p)].holder = p
ghost relation IsHoldingBothForks (p : philosopher) :=
  (forks (LeftFork p)).holder = p ∧ (forks (RightFork p)).holder = p
-- BothForksAreClean(p) == forks[LeftFork(p)].clean /\ forks[RightFork(p)].clean
ghost relation BothForksAreClean (p : philosopher) :=
  (forks (LeftFork p)).clean ∧ (forks (RightFork p)).clean
-- CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)
ghost relation CanEat (p : philosopher) := IsHoldingBothForks p ∧ BothForksAreClean p

-- Init == /\ forks = [fork \in 1..NP |-> [holder |-> IF fork = 2 THEN 1 ELSE fork, clean |-> FALSE]]
--         /\ hungry = [self \in 1..NP |-> TRUE] /\ pc = [self \in ProcSet |-> "Loop"]
after_init {
  forks F := { holder := if F = ph 2 then ph 1 else F, clean := false }
  hungry P := true
  pc P := Loop
}

/-
Loop(self) == /\ pc[self] = "Loop"
              /\ IF forks[LeftFork(self)].holder = self /\ ~forks[LeftFork(self)].clean
                   THEN forks' = [forks EXCEPT ![LeftFork(self)] = [holder |-> LeftPhilosopher(self), clean |-> TRUE]]
                   ELSE IF forks[RightFork(self)].holder = self /\ ~forks[RightFork(self)].clean
                          THEN forks' = [forks EXCEPT ![RightFork(self)] = [holder |-> RightPhilosopher(self), clean |-> TRUE]]
                          ELSE forks' = forks
              /\ IF hungry[self] THEN IF CanEat(self) THEN pc' = [pc EXCEPT ![self] = "Eat"]
                                                      ELSE pc' = [pc EXCEPT ![self] = "Loop"]
                                 ELSE pc' = [pc EXCEPT ![self] = "Think"]
              /\ UNCHANGED hungry
-/
action _Loop (self : philosopher) {
  require pc self = Loop
  -- `CanEat` is a `define` operator, so it must read the *unprimed* `forks`.
  let canEat := CanEat self
  if (forks (LeftFork self)).holder = self ∧ ¬ (forks (LeftFork self)).clean then
    forks (LeftFork self) := { holder := LeftPhilosopher self, clean := true }
  else if (forks (RightFork self)).holder = self ∧ ¬ (forks (RightFork self)).clean then
    forks (RightFork self) := { holder := RightPhilosopher self, clean := true }
  if hungry self then
    if canEat then
      pc self := Eat
    else
      pc self := Loop
  else
    pc self := Think
}

-- Think(self) == /\ pc[self] = "Think" /\ hungry' = [hungry EXCEPT ![self] = TRUE] /\ pc' = [pc EXCEPT ![self] = "Loop"] /\ forks' = forks
action _Think (self : philosopher) {
  require pc self = Think
  hungry self := true
  pc self := Loop
}

-- Eat(self) == /\ pc[self] = "Eat" /\ hungry' = [hungry EXCEPT ![self] = FALSE]
--              /\ forks' = [forks EXCEPT ![LeftFork(self)].clean = FALSE, ![RightFork(self)].clean = FALSE]
--              /\ pc' = [pc EXCEPT ![self] = "Loop"]
action _Eat (self : philosopher) {
  require pc self = Eat
  hungry self := false
  forks (LeftFork self) := { forks (LeftFork self) with clean := false }
  forks (RightFork self) := { forks (RightFork self) with clean := false }
  pc self := Loop
}

-- ShareFork(p, q) == {LeftFork(p), RightFork(p)} \cap {LeftFork(q), RightFork(q)} /= {}
ghost relation ShareFork (p q : philosopher) :=
  LeftFork p = LeftFork q ∨ LeftFork p = RightFork q ∨
  RightFork p = LeftFork q ∨ RightFork p = RightFork q

-- ExclusiveAccess == \A p,q \in 1..NP: p /= q /\ ShareFork(p, q) => ~(pc[p] = "Eat" /\ pc[q] = "Eat")
invariant [ExclusiveAccess]
  ∀ p q : philosopher, p ≠ q ∧ ShareFork p q → ¬ (pc p = Eat ∧ pc q = Eat)

-- ENABLED <<Philosopher(self)>>_vars, the enabling condition of WF_vars(Philosopher(self))
ghost relation EnabledPhilosopher (self : philosopher) :=
  pc self ≠ Loop
  ∨ ((forks (LeftFork self)).holder = self ∧ ¬ (forks (LeftFork self)).clean)
  ∨ ((forks (RightFork self)).holder = self ∧ ¬ (forks (RightFork self)).clean)
  ∨ ¬ hungry self
  ∨ CanEat self

-- Spec == /\ Init /\ [][Next]_vars /\ \A self \in 1..NP : WF_vars(Philosopher(self))
-- Philosopher(self) == Loop(self) \/ Think(self) \/ Eat(self)
-- NobodyStarves == \A p \in 1..NP: []<>(~hungry[p])
temporal (only := check) [NobodyStarves]
  (∀ self, (◇ □ ⌜ EnabledPhilosopher self ⌝) →
    □ ◇ ((T(_Loop self) ∨ T(_Think self) ∨ T(_Eat self)) ∧ ⌜ EnabledPhilosopher self ⌝))
  → ∀ p, □ ◇ ⌜ ¬ hungry p ⌝

-- DiningPhilosophers.cfg does not set CHECK_DEADLOCK FALSE, so TLC checks deadlock.
termination false

#gen_spec

def theory5 : Theory (Fin 5) pcLabel :=
  { succ := fun p => p + 1,
    pred := fun p => p - 1,
    ph := fun k => ⟨(k - 1) % 5, Nat.mod_lt _ (by omega)⟩ }

-- TLC on DiningPhilosophers.cfg (NP = 5): 67 distinct states.
--#model_check { philosopher := Fin 5 } theory5
--#temporal_check { philosopher := Fin 5 } theory5
