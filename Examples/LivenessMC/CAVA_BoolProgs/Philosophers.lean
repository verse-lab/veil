module

public import Veil

-- CAVA_LTL_Modelchecker/BoolProgs/Programs/BoolProgs_Philosophers.thy, `dining` at n=3
-- (matches `demo_phil_chosen = chose_prog (STR ''P'') 3` in CAVA_Impl.thy). AFP entry:
-- https://www.isa-afp.org/entries/CAVA_LTL_Modelchecker.html. Fork index i+1 wraps mod 3
-- (philosopher 2 shares its second fork with philosopher 0). Actions are 3 copies (i=0,1,2)
-- of `dining`'s per-philosopher template; the comments below are given once, on the i=0 copies.
veil module BoolProgPhilosophers

individual free0 : Bool
individual free1 : Bool
individual free2 : Bool
individual one0 : Bool
individual one1 : Bool
individual one2 : Bool
individual eat0 : Bool
individual eat1 : Bool
individual eat2 : Bool

#gen_state

after_init {
  free0 := true
  free1 := true
  free2 := true
  one0 := false
  one1 := false
  one2 := false
  eat0 := false
  eat1 := false
  eat2 := false
}

-- ¬eat[i] ∧ free[i]: one[i],free[i] := TT,FF
action pickup1_0 { require eat0 = false ∧ free0 = true; one0 := true; free0 := false }
-- one[i] ∧ free[i+1]: one[i],free[i+1],eat[i] := FF,FF,TT
action pickup2_0 { require one0 = true ∧ free1 = true; one0 := false; free1 := false; eat0 := true }
-- eat[i]: free[i],free[i+1],eat[i] := TT,TT,FF
action putdown_0 { require eat0 = true; free0 := true; free1 := true; eat0 := false }

action pickup1_1 { require eat1 = false ∧ free1 = true; one1 := true; free1 := false }
action pickup2_1 { require one1 = true ∧ free2 = true; one1 := false; free2 := false; eat1 := true }
action putdown_1 { require eat1 = true; free1 := true; free2 := true; eat1 := false }

action pickup1_2 { require eat2 = false ∧ free2 = true; one2 := true; free2 := false }
action pickup2_2 { require one2 = true ∧ free0 = true; one2 := false; free0 := false; eat2 := true }
action putdown_2 { require eat2 = true; free2 := true; free0 := true; eat2 := false }

safety [mutex01] ¬(eat0 = true ∧ eat1 = true)
safety [mutex12] ¬(eat1 = true ∧ eat2 = true)
safety [mutex20] ¬(eat2 = true ∧ eat0 = true)

-- Same property as the CAVA/Isabelle `demo_philosophers` binary: G (F (eat 0)).
-- Counterexample: the deadlock in which every philosopher holds one fork and nobody eats.
-- Philosophers 1 and 2 trading their shared fork forever, starving philosopher 0, is another.
liveness [φPhil0EventuallyEats] □ ◇ ⌜ eat0 = true ⌝

-- Not checked in the corresponding Isabelle demo, nor here: `#liveness_check` stops at the
-- counterexample to `φPhil0EventuallyEats` before reaching the properties below.
liveness [φMutex] □ (¬ (⌜ eat0 = true ⌝ ∧ ⌜ eat1 = true ⌝) ∧ ¬ (⌜ eat1 = true ⌝ ∧ ⌜ eat2 = true ⌝) ∧ ¬ (⌜ eat2 = true ⌝ ∧ ⌜ eat0 = true ⌝))

-- Not checked in the corresponding Isabelle demo, nor here (see above).
liveness [φSomeoneEats] ◇ (⌜ eat0 = true ⌝ ∨ ⌜ eat1 = true ⌝ ∨ ⌜ eat2 = true ⌝)

#gen_spec

-- Checks every `liveness` property above in declaration order, stopping at the first counterexample.
set_option veil.violationIsError false in
#liveness_check {}

end BoolProgPhilosophers
