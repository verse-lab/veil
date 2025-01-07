import Veil.DSL
import Examples.DSL.Std
-- https://github.com/aman-goel/ivybench/blob/master/distai/ivy/blockchain.ivy

section Blockchain
open Classical

type node
type block
type transaction
type time

instantiate tot : TotalOrder time

immutable relation leader : node → time → Prop

relation honest : node → Prop
relation broadcastable : node → block → time → Prop
relation broadcasted : node → Prop

relation block_found : node → block → time → Prop
relation block_confirmed : node → block → time → Prop

immutable relation transaction_time : transaction → time → Prop

relation transaction_in_block : transaction → block → Prop
relation transaction_confirmed : transaction → node → Prop

#gen_state Blockchain

assumption leader N1 T ∧ leader N2 T → N1 = N2
assumption leader N T1 ∧ leader N T2 → T1 = T2
assumption transaction_time TR T1 ∧ transaction_time TR T2 → T1 = T2

after_init {
    block_found N B T := False;
    block_confirmed N B T := False;
    transaction_in_block TR B := False;
    transaction_confirmed TR N := False;
    broadcasted N := False;
    broadcastable N B T := False
}

action find_block (n : node) (b : block) (t: time) = {
  require leader n t;
  block_found n b t := True
}

action add_transaction (tr : transaction) (b : block) = {
  transaction_in_block tr b := True
}

action begin_broadcast (n : node) (b : block) (t : time) = {
  require leader n t ∧ block_found n b t ∧ ¬ broadcasted n;
  broadcastable n b t := True
}

action begin_broadcast_adversary (n : node) (b : block) (t : time) = {
  require ¬ honest n;
  broadcastable n b t := True
}

action byzantine_broadcast (n : node) (b : block) (t : time) = {
  require broadcastable n b t;
  require honest n ∧ transaction_time TR T ∧ tot.le T t ∧ ¬ transaction_confirmed TR n → transaction_in_block TR b;
  require honest n ∧ transaction_in_block TR b → transaction_time TR T ∧ tot.le T t ∧ ¬ transaction_confirmed TR n;
  -- FIXME: why doesn't `block_confirmed N B t := *` work here?
  fresh havoc : Prop in
  block_confirmed N B t := havoc;
  broadcasted n := True;
  broadcastable n b t := False;
  transaction_confirmed TR N := transaction_confirmed TR N ∨ ((transaction_in_block TR b ∧ honest n) ∨ (¬ honest n ∧ transaction_confirmed TR N))
  -- FIXME:
  -- assume honest N → ¬ (B1 ≠ B2 ∧ block_confirmed N B1 t ∧ block_confirmed N B2 t);
  -- assume honest N1 ∧ honest N2 → (block_confirmed N1 b t ∧ block_confirmed N2 b t) ∨ (¬ block_confirmed N1 B t ∧ ¬ block_confirmed N2 B t);
  -- assume honest n ∧ honest N → block_confirmed N b t
}

action sabotage (n: node) = {
    require ¬ honest n;
    fresh havoc1 : Prop in
    block_confirmed n B T := havoc1;
    fresh havoc2 : Prop in
    transaction_confirmed TR n := havoc2
}

safety (honest N1 ∧ honest N2) → (block_confirmed N1 B T ∧ block_confirmed N2 B T) ∨ (¬ block_confirmed N1 B T ∧ ¬ block_confirmed N2 B T)
    ∧ (honest N1 ∧ honest N2) → (transaction_confirmed TR N1 ∧ transaction_confirmed TR N2) ∨ (¬ transaction_confirmed TR N1 ∧ ¬ transaction_confirmed TR N2)
    ∧ (honest N ∧ leader N T2 ∧ transaction_time TR T1 ∧ tot.le T1 T2 ∧ broadcasted N ∧ honest N1) → transaction_confirmed TR N1


invariant block_found N1 B1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1
invariant leader N1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1
invariant leader N1 TI1  ∨ ¬ block_found N1 B1 TI1
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI2  ∨ ¬ block_found N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1  ∨ ¬ broadcastable N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI2  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI2  ∨ ¬ block_found N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ block_found N1 B1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ leader N1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ transaction_time TR1 TI1  ∨ ¬ transaction_time TR1 TI2)

#gen_spec Blockchain

#check_invariants

end Blockchain
