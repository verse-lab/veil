import Veil.DSL

-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/distai/ivy/Ricart-Agrawala.ivy


section RicartAgrawala
open Classical

type node

relation requested : node → node → Prop
relation replied : node → node → Prop
relation holds : node → Prop

#gen_state RicartAgrawala

after_init {
  requested _ _ := False;
  replied _ _ := False;
  holds _ := False
}

action request (requester: node) (responder : node) = {
  require ¬ requested requester responder;
  require requester ≠ responder;
  requested requester responder := True
}

action reply (requester: node) (responder: node) = {
    require ¬ replied requester responder;
    require ¬ holds responder;
    require ¬ replied responder requester;
    require requested requester responder;
    require requester ≠ responder;
    requested requester responder := false;
    replied requester responder := true
}

action enter (requester: node) = {
  require (N ≠ requester) → replied requester N;
  holds requester := True
}

action leave (requester : node) = {
  require holds requester;
  holds requester := False;
  replied requester A := False
}

#gen_spec RicartAgrawala


safety [million] (holds N1 ∧ holds N2) → N1 = N2

invariant [manually_discovered] True ∧ True --∀ requester responder, replied requester responder → ¬ holds responder --holds A ↔ ∃ B, replied B A

#check_invariants



end RicartAgrawala
