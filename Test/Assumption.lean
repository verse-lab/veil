import Veil

set_option linter.unusedVariables false

veil module Blockchain

type node
type block
type transaction
type time

instantiate tot : TotalOrder time

immutable relation leader : node → time → Bool

relation honest : node → Bool
relation broadcastable : node → block → time → Bool
relation broadcasted : node → Bool

relation block_found : node → block → time → Bool
relation block_confirmed : node → block → time → Bool

immutable relation transaction_time : transaction → time → Bool

relation transaction_in_block : transaction → block → Bool
relation transaction_confirmed : transaction → node → Bool

#gen_state

assumption leader N1 T ∧ leader N2 T → N1 = N2
assumption leader N T1 ∧ leader N T2 → T1 = T2

after_init {
    block_found N B T := false;
    block_confirmed N B T := false;
    transaction_in_block TR B := false;
    transaction_confirmed TR N := false;
    broadcasted N := false;
    broadcastable N B T := false
}
assumption transaction_time TR T1 ∧ transaction_time TR T2 → T1 = T2

action find_block (n : node) (b : block) (t: time) {
  require leader n t;
  block_found n b t := true
}

invariant true

#gen_spec

end Blockchain
