module

public import Veil

veil module Traffic
-------------------------------- MODULE traffic ------------------------------

-- src: https://github.com/Apress/practical-tla-plus/blob/master/Chapter%206/traffic.tla

enum Color = {red, green}

enum ProcSet = {light, car}
enum states = {Cycle, Drive, Done}
individual at_light : Bool
individual LIGHT : Color
relation pc (P : ProcSet) (S : states)

#gen_state

-- Init == (* Global variables *)
--         /\ at_light = TRUE
--         /\ light = "red"
--         /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
--                                         [] self = "car" -> "Drive"]
after_init {
  at_light := true
  LIGHT := red
  pc P S := if P == light then S == Cycle else S == Drive
}

-- Cycle == /\ pc["light"] = "Cycle"
--          /\ IF at_light
--                THEN /\ light' = NextColor(light)
--                     /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
--                ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
--                     /\ light' = light
--          /\ UNCHANGED at_light
action Cycle {
  require pc light Cycle
  if at_light then
    -- NextColor: red -> green, green -> red
    LIGHT := if LIGHT == red then green else red
    pc light S := S == Cycle
  else
    pc light S := S == Done
}

-- Drive == /\ pc["car"] = "Drive"
--          /\ light = "green"
--          /\ at_light' = FALSE
--          /\ pc' = [pc EXCEPT !["car"] = "Done"]
--          /\ light' = light
action Drive {
  require pc car Drive
  require LIGHT == green
  at_light := false
  pc car S := S == Done
}

/- Corresponding to Line 67:
`Termination == <>(\A self \in ProcSet: pc[self] = "Done")`
in Traffic.tla. The explaination has been given in `MutexViolation.lean`,
which is the same as `action Terminating` there. -/
action shutter_termination {
  require (∀p, pc p Done)
}

invariant [pc_unique] pc P S ∧ pc P T → S = T
safety [puzzle_unsolvable]
  -- Car is always at the light (negated goal)
  at_light = true

#time #gen_spec

-- TLC checks this spec with `Benchmarks/TLA/Traffic.cfg`, which sets no constants and checks no
-- invariant.
-- The check below finds a violation of `puzzle_unsolvable`, which claims that the car stays at
-- the light: the trace shows the car driving off.
-- `set_option veil.violationIsError false in` reports that violation without failing the build.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `ProcSet := ProcSet_IndT`, `Color := Color_IndT`, `states := states_IndT`: each `enum` above
--   is a type parameter, and these give it its generated `_IndT` type. That is the default, so
--   these items could be left out. The cfg has no counterpart: in TLA+, the processes are
--   `"light"` and `"car"`, and the colors and labels are strings.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields. There are none,
-- hence `{}`.
--
-- The other settings of the cfg:
-- * The cfg checks no invariant. This module adds `puzzle_unsolvable`, and `pc_unique`, which
--   checks that the relation `pc` gives each process a single label.
-- * `CHECK_DEADLOCK FALSE`: this module has no `termination` clause, so Veil reports no
--   deadlocks either.
-- * `PROPERTY Termination`, commented out in the cfg: a temporal property, which Veil does not
--   check.
-- Options:
-- * The check names no mode, so its search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
set_option veil.violationIsError false in
#model_check { ProcSet := ProcSet_IndT, Color := Color_IndT, states := states_IndT } {}

end Traffic
