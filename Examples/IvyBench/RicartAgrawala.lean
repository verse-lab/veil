import Veil

-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/distai/ivy/Ricart-Agrawala.ivy


veil module RicartAgrawala


type node

relation requested (n1 : node) (n2 : node)
relation replied (n1 : node) (n2 : node)
relation holds (n : node)

#gen_state

after_init {
  requested N1 N2 := False;
  replied N1 N2 := False;
  holds N := False
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
    requested requester responder := False;
    replied requester responder := True
}

action enter (requester: node) = {
  require ∀ N, (N ≠ requester) → replied requester N;
  holds requester := True
}

action leave (requester : node) = {
  require holds requester;
  holds requester := False;
  replied requester N := False
}

safety [mutual_exclusion] (holds N1 ∧ holds N2) → N1 = N2
invariant N1 ≠ N2 → ¬(replied N1 N2 ∧ replied N2 N1)
invariant (N1 ≠ N2 ∧  holds N1) → replied N1 N2

#gen_spec

#time #check_invariants


end RicartAgrawala
