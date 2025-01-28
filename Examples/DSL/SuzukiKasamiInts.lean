import Veil.DSL
import Examples.DSL.Std

-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/suzuki_kasami_int.ivy

namespace SuzukiKasamiInts
open Classical

type node
notation "seq_t" => Int
immutable individual init_node : node
@[actSimp] abbrev next : seq_t → seq_t → Prop := λ x y => x + 1 = y


-- State

--- Nodes
relation n_have_privilege : node → Prop
relation n_requesting : node → Prop
function n_RN : node → node → seq_t
-- the sequence number of the most recently granted request by `node`
function n_token_seq : node → seq_t

--- Requests
relation reqs : node → node → seq_t → Prop

--- Tokens
relation t_for : seq_t → node → Prop
function t_LN : seq_t → node → seq_t
relation t_q : seq_t → node → Prop

--- Critical section
relation crit : node → Prop

#gen_state

after_init {
  n_have_privilege N := N = init_node;
  n_requesting N := False;
  n_RN N M := 0;
  n_token_seq N := if N = init_node then 1 else 0;

  reqs N M I := False;

  t_for I N := I = 1 ∧ N = init_node;
  t_LN I N := 0;
  t_q I N := False;

  crit N := False
}

action request (n : node) = {
  require ¬ n_requesting n;
  n_requesting n := True;
  if (¬ n_have_privilege n) then
    let k := (n_RN n n) + 1
    n_RN n n := k;
    reqs N n (n_RN n n) := N ≠ n
}

-- node `n` receiving a request from `m` with sequence number `r`
action rcv_request (n : node) (m : node) (r : seq_t) = {
  require reqs n m r;
  n_RN n m := if r ≤ (n_RN n m) then n_RN n m else r;
  if (n_have_privilege n ∧ ¬ n_requesting n ∧ next (t_LN (n_token_seq n) m) (n_RN n m)) then
    n_have_privilege n := False;
    let k : seq_t := (n_token_seq n) + 1
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

action rcv_privilege (n: node) (t: seq_t) = {
  require t_for t n;
  require (n_token_seq n) < t;
  n_have_privilege n := True;
  n_token_seq n := t
}

action exit (n : node) = {
  require crit n;
  crit n := False;
  n_requesting n := False;
  t_LN (n_token_seq n) n := n_RN n n;
  t_q (n_token_seq n) N := next (t_LN (n_token_seq n) N) (n_RN n N);
  if m : (t_q (n_token_seq n) m) then
    t_q (n_token_seq n) m := False;
    n_have_privilege n := False;
    let k : seq_t := (n_token_seq n) + 1
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

-- Invariants
invariant [mutex] (crit N ∧ crit M) → N = M
invariant [single_privilege] (n_have_privilege N ∧ n_have_privilege M) → N = M
invariant [allowed_in_crit] (crit N) → (n_have_privilege N ∧ n_requesting N)
invariant [unique_tokens] ((t_for I N) ∧ (t_for I M)) → N = M
invariant [corresponding_tokens] ((n_token_seq N) ≠ 0) → t_for (n_token_seq N) N
invariant [current_privilege_latest_token_1] ((n_have_privilege N) ∧ N ≠ M) → (n_token_seq M) < (n_token_seq N)
invariant [current_privilege_latest_token_2] ((n_have_privilege N) ∧ (t_for I M)) → I ≤ (n_token_seq N)
-- invariant [current_privilege_latest_token_3] (∀ n, ¬ n_have_privilege n) → (∃ i m, t_for i m ∧ ∀ w, seq.lt (n_token_seq w) i)
-- invariant [current_privilege_latest_token_4] ((t_for I N) ∧ (∀ w, seq.lt (n_token_seq w) I)
--     ∧ (t_for J M) ∧ (∀ w, seq.lt (n_token_seq w) J))
--     → (I = J ∧ N = M)
invariant [no_request_to_self] (reqs N M I) → N ≠ M
invariant [no_consecutive_privilege] ((t_for I N) ∧ (next J I) ∧ (t_for J M)) → N ≠ M
invariant [token_relation] ((t_for I N) ∧ (t_for J M) ∧ I < J) → I ≤ (n_token_seq N)

#gen_spec

set_option sauto.smt.solver "cvc5"
set_option sauto.smt.translator "lean-smt"

set_option trace.sauto.query true

  @[invProof]
  theorem SuzukiKasamiInts.rcv_request_SuzukiKasamiInts.no_consecutive_privilege :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_request.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.no_consecutive_privilege node node_dec node_ne st' :=
    by
      dsimp only [invSimp, SuzukiKasamiInts.rcv_request.ext]; intros st; sdestruct_hyps
      first
      | intro ass_ inv_; intro (st' : @State node);
        unhygienic cases st'; revert ass_ inv_; dsimp only
      | try dsimp only
        try simp only [exists_imp, and_imp]
        unhygienic intros
        try simp only [ifSimp]
      first
      | (try split_ifs with exists_imp, and_imp)
      { simp [actSimp] at *
        sauto_all
        }

#exit

  @[invProof]
  theorem SuzukiKasamiInts.rcv_request_SuzukiKasamiInts.token_relation :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_request.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.token_relation node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_request.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.mutex :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) => @SuzukiKasamiInts.mutex node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.single_privilege :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.single_privilege node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.allowed_in_crit :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.allowed_in_crit node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.unique_tokens :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.unique_tokens node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.corresponding_tokens :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.corresponding_tokens node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.current_privilege_latest_token_1 :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.current_privilege_latest_token_1 node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.current_privilege_latest_token_2 :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.current_privilege_latest_token_2 node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.no_request_to_self :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.no_request_to_self node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.no_consecutive_privilege :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.no_consecutive_privilege node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.rcv_privilege_SuzukiKasamiInts.token_relation :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.rcv_privilege.ext node node_dec node_ne) st
              fun _ (st' : @State node) =>
              @SuzukiKasamiInts.token_relation node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.rcv_privilege.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.mutex :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.mutex node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.single_privilege :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.single_privilege node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.allowed_in_crit :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.allowed_in_crit node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.unique_tokens :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.unique_tokens node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.corresponding_tokens :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.corresponding_tokens node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.current_privilege_latest_token_1 :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.current_privilege_latest_token_1 node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.current_privilege_latest_token_2 :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.current_privilege_latest_token_2 node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.no_request_to_self :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.no_request_to_self node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.no_consecutive_privilege :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.no_consecutive_privilege node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext

  @[invProof]
  theorem SuzukiKasamiInts.exit_SuzukiKasamiInts.token_relation :
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiInts.exit.ext node node_dec node_ne) st fun _ (st' : @State node) =>
              @SuzukiKasamiInts.token_relation node node_dec node_ne st' :=
    by solve_wlp_clause SuzukiKasamiInts.exit.ext



end SuzukiKasamiInts
