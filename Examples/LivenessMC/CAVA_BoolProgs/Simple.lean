module

public import Veil

-- CAVA_LTL_Modelchecker/BoolProgs/Programs/BoolProgs_Simple.thy, `simple` at n=4 (matches
-- `demo_simple_chosen = chose_prog (STR ''S'') 4` in CAVA_Impl.thy). AFP entry:
-- https://www.isa-afp.org/entries/CAVA_LTL_Modelchecker.html. `clear0..clear3` are 4 copies
-- of `simple_prog`'s `V i → var[i]:=FF` template; the comment below is given once, on `clear0`.
veil module BoolProgSimple

individual v0 : Bool
individual v1 : Bool
individual v2 : Bool
individual v3 : Bool

#gen_state

after_init {
  v0 := true
  v1 := true
  v2 := true
  v3 := true
}

-- V i: var[i] := FF
action clear0 { require v0 = true; v0 := false }
action clear1 { require v1 = true; v1 := false }
action clear2 { require v2 = true; v2 := false }
action clear3 { require v3 = true; v3 := false }

safety [boolsAreBools] (v0 = true ∨ v0 = false)

-- Same property as the CAVA/Isabelle `demo_simple` binary: F (G (not (var 0))).
temporal [φV0EventuallyStaysOff] ◇ □ ⌜ v0 = false ⌝

-- Not checked in the corresponding Isabelle demo; holds.
temporal [φTerminates] ◇ □ ⌜ ¬v0 ∧ ¬v1 ∧ ¬v2 ∧ ¬v3 ⌝

-- Not checked in the corresponding Isabelle demo. Fails: every run clears `v0` for good, so this
-- is the property reported below, with its counterexample.
temporal [φInfinitelyOn] □ ◇ ⌜ v0 = true ⌝

#gen_spec

-- Checks every `liveness` property above in declaration order, stopping at the first counterexample.
set_option veil.violationIsError false in
#liveness_check {}

end BoolProgSimple
