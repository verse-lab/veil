import Veil

-- Regression test for the following bug reported by Mark Tuttle:
-- https://leanprover.zulipchat.com/#narrow/channel/537982-Veil/topic/Brittle.20invariance.20checking.20in.20the.20initial.20state/with/573570686
-- https://github.com/ufmg-smite/lean-smt/issues/215

veil module ABP

type value

immutable function p_msgs: Nat → value
immutable individual p_tail: Nat
individual p_bit: Bool
individual p_next: Nat
function c_msgs: Nat -> value
individual c_tail: Nat
individual c_bit: Bool
function p2c_value: Nat → value
function p2c_bit: Nat → Bool
individual p2c_head: Nat
individual p2c_tail: Nat
function c2p_bit: Nat → Bool
individual c2p_head: Nat
individual c2p_tail: Nat
individual first_new: Nat

#gen_state

after_init {

  p_next := 0;

  c_tail := 0;
  c_bit := !p_bit;

  p2c_head := 0;
  p2c_tail := 0;

  c2p_head := 0;
  c2p_tail := 0;

  first_new := 0;
}


-- action p_send {
--   require p_next < p_tail

--   p2c_value p2c_tail := p_msgs p_next;
--   p2c_bit p2c_tail := p_bit;
--   p2c_tail := p2c_tail + 1;
-- }

action p_receive {
  require c2p_head < c2p_tail

  let bit := c2p_bit c2p_head;
  c2p_head := c2p_head + 1;

  if bit == p_bit then
    p_bit := !p_bit;
    p_next := p_next + 1;
    first_new := p2c_tail; -- ghost (may be off by one)
}

action c_send {
  c2p_bit c2p_tail := c_bit;
  c2p_tail := c2p_tail + 1;
}

action c_receive {
  require p2c_head < p2c_tail

  let bit := p2c_bit p2c_head;
  let val := p2c_value p2c_head;
  p2c_head := p2c_head + 1;

  if bit != c_bit then
    c_bit := bit;
    c_msgs c_tail := val;
    c_tail := c_tail + 1;
    first_new := c2p_tail;  -- ghost (may be off by one)
}

action p2c_fail {
  require p2c_head < p2c_tail

  p2c_head := p2c_head + 1;
}

action c2p_fail {
  require c2p_head < c2p_tail

  c2p_head := c2p_head + 1;
}

invariant p_bit = c_bit → first_new <= c2p_tail
invariant p_bit != c_bit → first_new <= p2c_tail

invariant (p_bit = c_bit ∧ p2c_head <= N ∧ N < p2c_tail ∧ N ≥ 0)→ p2c_bit N = p_bit
invariant (p_bit = c_bit ∧ c2p_head <= N ∧ N < c2p_tail ∧ N < first_new ∧ N ≥ 0) → c2p_bit N != p_bit
invariant (p_bit = c_bit ∧ c2p_head <= N ∧ N < c2p_tail ∧ first_new <= N ∧ N ≥ 0) → c2p_bit N = p_bit

invariant (p_bit != c_bit ∧ c2p_head <= N ∧ N < c2p_tail ∧ N ≥ 0) → c2p_bit N != p_bit
invariant (p_bit != c_bit ∧ p2c_head <= N ∧ N < p2c_tail ∧ N < first_new ∧ N ≥ 0) → p2c_bit N != p_bit
invariant (p_bit != c_bit ∧ p2c_head <= N ∧ N < p2c_tail ∧ first_new <= N ∧ N ≥ 0) → p2c_bit N = p_bit

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
  inv_3 ... ✅
  inv_4 ... ✅
  inv_5 ... ✅
  inv_6 ... ✅
  inv_7 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  c_send
    doesNotThrow ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
    inv_4 ... ✅
    inv_5 ... ✅
    inv_6 ... ✅
    inv_7 ... ✅
  c_receive
    doesNotThrow ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
    inv_4 ... ✅
    inv_5 ... ✅
    inv_6 ... ✅
    inv_7 ... ✅
  p2c_fail
    doesNotThrow ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
    inv_4 ... ✅
    inv_5 ... ✅
    inv_6 ... ✅
    inv_7 ... ✅
  c2p_fail
    doesNotThrow ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
    inv_4 ... ✅
    inv_5 ... ✅
    inv_6 ... ✅
    inv_7 ... ✅
  p_receive
    doesNotThrow ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
    inv_4 ... ✅
    inv_5 ... ✅
    inv_6 ... ✅
    inv_7 ... ✅
-/
#guard_msgs in
#check_invariants

end ABP
