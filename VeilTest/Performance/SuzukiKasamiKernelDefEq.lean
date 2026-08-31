import Veil

veil module SuzukiKasami

type node
type seq_t
immutable individual init_node : node

instantiate seq : TotalOrderWithMinimum seq_t

function n_have_privilege : node → Bool
relation n_requesting : node → Bool
function n_RN : node → node → seq_t
function n_token_seq : node → seq_t

relation reqs : node → node → seq_t → Bool

relation t_for : seq_t → node → Bool
function t_LN : seq_t → node → seq_t
relation t_q : seq_t → node → Bool

relation crit : node → Bool

#gen_state

action succ (n : seq_t) {
  let k : seq_t ← pick
  assume seq.next n k;
  return k
}

action request (n : node) {
  require ¬ n_requesting n;
  n_requesting n := true;
  if (¬ n_have_privilege n) then
    let k ← succ (n_RN n n)
    n_RN n n := k;
    reqs N n (n_RN n n) := decide $ N ≠ n
}

end SuzukiKasami
