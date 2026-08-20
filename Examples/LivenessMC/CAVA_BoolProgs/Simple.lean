import Veil

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
liveness [φV0EventuallyStaysOff] ◇ □ ⌜ v0 = false ⌝

-- Not checked in the corresponding Isabelle demo.
liveness [φTerminates] ◇ □ ⌜ ¬v0 ∧ ¬v1 ∧ ¬v2 ∧ ¬v3 ⌝

-- Not checked in the corresponding Isabelle demo.
liveness [φInfinitelyOn] □ ◇ ⌜ v0 = true ⌝

#gen_spec

#model_check {}

#eval Veil.LivenessMC.printCheckResult "BoolProgSimple" "◇□(¬v0)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (φV0EventuallyStaysOff Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

-- Not checked in Isabelle; left commented out, uncomment as a sanity check only.
/-
#eval Veil.LivenessMC.printCheckResult "BoolProgSimple" "◇□(allOff)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (φTerminates Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))
-/

-- Not checked in Isabelle; left commented out, uncomment as a sanity check only.
/-
#eval Veil.LivenessMC.printCheckResult "BoolProgSimple" "□◇(v0On)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (φInfinitelyOn Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))
-/

end BoolProgSimple
