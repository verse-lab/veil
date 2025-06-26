import Veil

veil module Blockchain

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

#gen_state

assumption leader N1 T ∧ leader N2 T → N1 = N2
assumption leader N T1 ∧ leader N T2 → T1 = T2

after_init {
    block_found N B T := False;
    block_confirmed N B T := False;
    transaction_in_block TR B := False;
    transaction_confirmed TR N := False;
    broadcasted N := False;
    broadcastable N B T := False
}

/-- error: All assumptions must be defined before the after_init declaration! -/
#guard_msgs in
assumption transaction_time TR T1 ∧ transaction_time TR T2 → T1 = T2

action find_block (n : node) (b : block) (t: time) = {
  require leader n t;
  block_found n b t := True
}

invariant True

#gen_spec

end Blockchain
