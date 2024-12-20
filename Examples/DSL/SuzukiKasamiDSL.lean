import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.NoPaxosDSL

section SuzukiKasami
open Classical

type node
type seq_t
individual init_node : node

instantiate seq : TotalOrderWithMinimum seq_t

-- State

--- Nodes
relation n_have_privilege : node → Prop
relation n_requesting : node → Prop
function n_RN : node → node → seq_t
function n_token_seq : node → seq_t

--- Requests
relation reqs : node → node → seq_t → Prop

--- Tokens
relation t_for : seq_t → node → Prop
function t_LN : seq_t → node → seq_t
relation t_q : seq_t → node → Prop

--- Critical section
relation crit : node → Prop

#gen_state SuzukiKasami

action succ (n : seq_t) = {
    fresh k : seq_t in
    require seq.next k n;
    return k
}

after_init {
  fresh init_node' : node in
  init_node := init_node';
  n_have_privilege N := N = init_node';
  n_requesting _ := False;
  n_RN _ _ := seq.zero;
  require ∀N, (N = init_node') → (seq.next seq.zero (n_token_seq N));
  require ∀N, (N ≠ init_node') → (n_token_seq N = seq.zero);

  reqs _ _ _ := False;

  t_for I N := (seq.next seq.zero I) ∧ N = init_node';
  t_LN _ _ := seq.zero;
  t_q _ _ := False;

  crit _ := False
}



action request (n : node) = {
  require ¬ n_requesting n;
  n_requesting n := True;
  if (¬ n_have_privilege n) {
    k : seq_t ← call !succ (n_RN n n) in
    n_RN n n := k;
    reqs N n (n_RN n n) := N ≠ n
  }
}

action rcv_request (n : node) (m : node) (r : seq_t) = {
  require reqs n m r;
  n_RN n m := if seq.le r (n_RN n m) then n_RN n m else r;
  if (n_have_privilege n ∧ ¬ n_requesting n ∧ seq.next (t_LN (n_token_seq n) m) (n_RN n m)) {
    n_have_privilege n := False;
    k : seq_t ← call !succ (n_token_seq n) in
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
  }
}

action rcv_privilege (n: node) (t: seq_t) = {
  require t_for t n;
  require seq.lt (n_token_seq n) t;
  n_have_privilege n := True;
  n_token_seq n := t
}

action exit (n : node) = {
  require crit n;
  crit n := False;
  n_requesting n := False;
  t_LN (n_token_seq n) n := n_RN n n;
  t_q (n_token_seq n) N := seq.next (t_LN (n_token_seq n) N) (n_RN n N);
  if m where (t_q (n_token_seq n) m) {
    t_q (n_token_seq n) m := False;
    n_have_privilege n := False;
    k : seq_t ← call !succ (n_token_seq n) in
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
  }
}

-- Invariants
invariant [mutex] (crit N ∧ crit M) → N = M
invariant [single_privilege] (n_have_privilege N ∧ n_have_privilege M) → N = M
invariant [allowed_in_crit] (crit N) → n_have_privilege N ∧ n_requesting N
invariant [unique_tokens] ((t_for I N) ∧ (t_for I M)) → N = M
invariant [corresponding_tokens] ((n_token_seq N) ≠ seq.zero) → t_for (n_token_seq N) N
invariant [current_privilege_latest_token_1] ((n_have_privilege N) ∧ N ≠ M) → seq.lt (n_token_seq M) (n_token_seq N)
invariant [current_privilege_latest_token_2] ((n_have_privilege N) ∧ (t_for I M)) → seq.le I (n_token_seq N)
invariant [current_privilege_latest_token_3] (∀ n, ¬ n_have_privilege n) → (∃ i m, t_for i m ∧ ∀ w, seq.lt (n_token_seq w) i)
invariant [current_privilege_latest_token_4] ((t_for I N) ∧ (∀ w, seq.lt (n_token_seq w) I)
    ∧ (t_for J M) ∧ (∀ w, seq.lt (n_token_seq w) J))
    → (I = J ∧ N = M)
invariant [no_request_to_self] (reqs N M I) → N ≠ M
invariant [no_consecutive_privilege] ((t_for I N) ∧ (seq.next J I) ∧ (t_for J M)) → N ≠ M
invariant [token_relation] ((t_for I N) ∧ (t_for J M) ∧ seq.lt I J) → seq.le I (n_token_seq N)

#gen_spec SuzukiKasami

end SuzukiKasami
