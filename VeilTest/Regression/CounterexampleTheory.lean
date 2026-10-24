module

public import Veil

/-! A counterexample to induction shows the theory: the constructors of an enum on one line, and
the other immutable components one per line, like the fields of a state. -/

veil module CounterexampleTheory

type node
immutable individual leader : node
immutable relation peer : node → node → Bool
individual holder : node

after_init {
  holder := leader
}

action pass (n : node) {
  require peer holder n
  holder := n
}

invariant [held] holder = leader

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  held ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  pass
    doesNotThrow ... ✅
    held ... ❌
      Counterexample (WP):
        Theory:
          leader = 1
          peer = {(0, 0), (0, 1), (1, 0), (1, 1)}
        Pre-state:
          holder = 1
        Action: pass(n=0)
      Counterexample (TR):
        Theory:
          leader = 1
          peer = {(0, 0), (0, 1), (1, 0), (1, 1)}
        Pre-state:
          holder = 1
        Action: pass(n=0)
        Post-state:
          holder = 0
-/
#guard_msgs in
#check_invariants

end CounterexampleTheory
