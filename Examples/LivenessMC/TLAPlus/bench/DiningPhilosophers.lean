module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/DiningPhilosophers/DiningPhilosophers.tla
-- Chandy-Misra "dirty fork" solution, NP = 5 as in DiningPhilosophers.cfg.

veil module DiningPhilosophers

-- CONSTANT NP; ASSUME NP \in Nat \ {0}. DiningPhilosophers.cfg sets NP = 5.
abbrev NP : Nat := 5
abbrev Phil := Fin NP

-- forks = [fork \in 1..NP |-> [holder |-> …, clean |-> …]]
function forkHolder : Phil → Phil
relation forkClean : Phil → Bool
-- hungry = [self \in 1..NP |-> TRUE]
relation hungry : Phil → Bool

-- pc = [self \in ProcSet |-> "Loop"]
enum PC = { Loop_S, Eat_S, Think_S }
function pc : Phil → PC

#gen_state

-- LeftFork(p) == p ; RightFork(p) == IF p = NP THEN 1 ELSE p + 1
ghost relation leftHeld (p : Phil) := forkHolder p = p
ghost relation rightHeld (p : Phil) := forkHolder (p + 1) = p

-- IsHoldingBothForks(p) /\ BothForksAreClean(p)
ghost relation canEat (p : Phil) :=
  forkHolder p = p ∧ forkHolder (p + 1) = p ∧ forkClean p ∧ forkClean (p + 1)

-- Init == forks = [fork |-> [holder |-> IF fork = 2 THEN 1 ELSE fork, clean |-> FALSE]]
--         /\ hungry = [self |-> TRUE] /\ pc = [self |-> "Loop"]
after_init {
  forkHolder F := if F = (1 : Phil) then (0 : Phil) else F
  forkClean F := false
  hungry P := true
  pc P := Loop_S
}

-- Loop(self): give away a dirty held fork (left first, then right), then decide to Eat (if
-- CanEat) or keep Looping while hungry, else start Thinking.
action loop (self : Phil) {
  require pc self = Loop_S
  if forkHolder self = self ∧ ¬forkClean self then
    forkHolder self := self - 1;
    forkClean self := true
  else
    if forkHolder (self + 1) = self ∧ ¬forkClean (self + 1) then
      forkHolder (self + 1) := self + 1;
      forkClean (self + 1) := true
    else
      pure ()
  if hungry self then
    if forkHolder self = self ∧ forkHolder (self + 1) = self
       ∧ forkClean self ∧ forkClean (self + 1) then
      pc self := Eat_S
    else
      pc self := Loop_S
  else
    pc self := Think_S
}

-- Eat(self) == pc[self] = "Eat" /\ hungry' = FALSE /\ both held forks become dirty
action eat (self : Phil) {
  require pc self = Eat_S
  hungry self := false
  forkClean self := false
  forkClean (self + 1) := false
  pc self := Loop_S
}

-- Think(self) == pc[self] = "Think" /\ hungry' = TRUE
action think (self : Phil) {
  require pc self = Think_S
  hungry self := true
  pc self := Loop_S
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

-- TypeOK == forks \in [1..NP -> [holder: 1..NP, clean: BOOLEAN]] /\ … — carried by the types.
-- ExclusiveAccess == \A p,q: p # q /\ ShareFork(p,q) => ~(pc[p] = "Eat" /\ pc[q] = "Eat")
-- ShareFork(p,q) == {LeftFork(p), RightFork(p)} \cap {LeftFork(q), RightFork(q)} /= {}
invariant [exclusiveAccess]
  ∀ p q : Phil, p ≠ q →
    (p = q + 1 ∨ q = p + 1 ∨ p = q) → ¬(pc p = Eat_S ∧ pc q = Eat_S)

-- NobodyStarves == \A p \in 1..NP: []<>(~hungry[p])
-- Not in the TLA+ source unconditionally: its .cfg only ever checks NobodyStarves under the fair
-- Spec.
-- Not checked on TLC.
temporal [nobodyStarves]
  (□ ◇ ⌜ hungry (0 : Phil) = false ⌝)
  ∧ (□ ◇ ⌜ hungry (1 : Phil) = false ⌝)
  ∧ (□ ◇ ⌜ hungry (2 : Phil) = false ⌝)
  ∧ (□ ◇ ⌜ hungry (3 : Phil) = false ⌝)
  ∧ (□ ◇ ⌜ hungry (4 : Phil) = false ⌝)

-- Spec's `\A self \in 1..NP: WF_vars(Philosopher(self))`. Philosopher(p) is the union of
-- Loop(p)/Eat(p)/Think(p), and exactly one of those three guards holds in every state (pc[p] is
-- one of the three labels), so Philosopher(p) is always enabled — `E(loop p)∨E(eat p)∨E(think p)`
-- is provably `⊤`, and weak fairness on it collapses to "infinitely often, philosopher p takes a
-- step". One conjunct per philosopher, hardcoded to NP = 5.
temporal [nobodyStarvesFair]
  ((□ (◇ ¬(E(loop (0:Phil)) ∨ E(eat (0:Phil)) ∨ E(think (0:Phil)))
       ∨ ◇ (T(loop (0:Phil)) ∨ T(eat (0:Phil)) ∨ T(think (0:Phil)))))
   ∧ (□ (◇ ¬(E(loop (1:Phil)) ∨ E(eat (1:Phil)) ∨ E(think (1:Phil)))
       ∨ ◇ (T(loop (1:Phil)) ∨ T(eat (1:Phil)) ∨ T(think (1:Phil)))))
   ∧ (□ (◇ ¬(E(loop (2:Phil)) ∨ E(eat (2:Phil)) ∨ E(think (2:Phil)))
       ∨ ◇ (T(loop (2:Phil)) ∨ T(eat (2:Phil)) ∨ T(think (2:Phil)))))
   ∧ (□ (◇ ¬(E(loop (3:Phil)) ∨ E(eat (3:Phil)) ∨ E(think (3:Phil)))
       ∨ ◇ (T(loop (3:Phil)) ∨ T(eat (3:Phil)) ∨ T(think (3:Phil)))))
   ∧ (□ (◇ ¬(E(loop (4:Phil)) ∨ E(eat (4:Phil)) ∨ E(think (4:Phil)))
       ∨ ◇ (T(loop (4:Phil)) ∨ T(eat (4:Phil)) ∨ T(think (4:Phil))))))
  → ((□ ◇ ⌜ hungry (0 : Phil) = false ⌝)
     ∧ (□ ◇ ⌜ hungry (1 : Phil) = false ⌝)
     ∧ (□ ◇ ⌜ hungry (2 : Phil) = false ⌝)
     ∧ (□ ◇ ⌜ hungry (3 : Phil) = false ⌝)
     ∧ (□ ◇ ⌜ hungry (4 : Phil) = false ⌝))

#gen_spec

#temporal_check [nobodyStarvesFair] compiled { PC := PC_IndT } {} (route := .fair)

end DiningPhilosophers
