module

public import Veil

veil module SFHub2

abbrev Loc := Fin 4
individual loc : Loc

after_init { loc := (0 : Loc) }

action toLeaf (l : Loc) {
  require loc = (0 : Loc) ∧ l ≠ (0 : Loc)
  loc := l
}
action toHub {
  require loc ≠ (0 : Loc)
  loc := (0 : Loc)
}

temporal [noFair] □ (⌜ loc = (0 : Loc) ⌝ → ◇ ⌜ loc = (1 : Loc) ⌝)

-- client 0: request = hub itself
-- client 1: own request/ack pair
temporal [goal]
  ((□ ◇ ⌜ loc = (0 : Loc) ⌝ → □ ◇ ⌜ loc = (1 : Loc) ⌝)
   ∧ (□ ◇ ⌜ loc = (2 : Loc) ⌝ → □ ◇ ⌜ loc = (3 : Loc) ⌝))
  → □ (⌜ loc = (0 : Loc) ⌝ → ◇ ⌜ loc = (1 : Loc) ⌝)

#gen_spec

-- set_option veil.violationIsError false in
#temporal_check {}

end SFHub2
