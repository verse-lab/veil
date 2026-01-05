import Veil
veil module traffic
-------------------------------- MODULE traffic ------------------------------

-- src: https://github.com/Apress/practical-tla-plus/blob/master/Chapter%206/traffic.tla

enum Color = {red, green}

enum ProcSet = {light, car}
enum states = {Cycle, Drive, Done}
individual at_light : Bool
individual LIGHT : Color
relation pc (P : ProcSet) (S : states)

#gen_state

after_init {
  at_light := true
  LIGHT := red
  pc P S := if P == light then S == Cycle else S == Drive
}

action Cycle {
  require pc light Cycle
  if at_light then
    -- NextColor: red -> green, green -> red
    LIGHT := if LIGHT == red then green else red
    pc light S := S == Cycle
  else
    pc light S := S == Done
}

action Drive {
  require pc car Drive
  require LIGHT == green
  at_light := false
  pc car S := S == Done
}

termination [all_done] (∀ P : ProcSet, pc P Done)
invariant [pc_unique] pc P S ∧ pc P T → S = T
safety [puzzle_unsolvable]
  -- Car is always at the light (negated goal)
  at_light = true

#time #gen_spec

#model_check { ProcSet := ProcSet_IndT, Color := Color_IndT, states := states_IndT } {}

end traffic
