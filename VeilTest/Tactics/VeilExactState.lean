module

public import Veil

/- Testing `veil_exact_state` tactic by using ghost relations. -/

veil module VeilExactState

type t
relation rel (x : t) (y : t)
individual pivot : t

#gen_state

ghost relation g (x : t) := rel x x ∧ (∀ y, rel x y → x = y)

after_init {
  rel X Y := false
}

action act1 (x y z u v w : t) {
  if x = y then
    require g w
    if y = z then
      require g u
      rel x z := true
    require g x
  rel u v := true
  require g u
  if u = v then
    if v = w then
      rel u w := true
      require g x
    require g z
    rel u u := true
  require g y
}

invariant true

/- The quantifier shadows the state field `pivot`. Inside an invariant, the
field view `pivot` is an ordinary `let` of `get pivot_conc`, so `veil_exact_state`,
which supplies the default state argument of `g`, finds the quantified `pivot`
by name and must fall back to `pivot_conc`. -/
invariant [ghost_under_shadowing_binder] ∀ pivot : t, g pivot → rel pivot pivot

#gen_spec

end VeilExactState
