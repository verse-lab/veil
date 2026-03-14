import Std
import Veil

namespace VeilTest.Deriving

-- Test 1: Enum-like (no arguments)
inductive Color where
  | red | green | blue
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd Color
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd Color

-- Test 2: Small inductive (1-2 constructors)
inductive SmallMsg where
  | ping (id : Nat)
  | pong (id : Nat) (ok : Bool)
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd SmallMsg
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd SmallMsg

-- Test 3: Medium inductive (4 constructors)
inductive MediumMsg (α : Type) where
  | request (sender : Nat) (payload : α)
  | response (sender : Nat) (payload : α) (ok : Bool)
  | ack (id : Nat)
  | nack (id : Nat) (reason : Nat)
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd (MediumMsg Nat)
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd (MediumMsg Nat)

-- Test 4: Large inductive (~8 constructors)
inductive BigMsg (node val : Type) where
  | prepare (sender : node) (value : val) (slot : Nat)
  | promise (sender : node) (slot : Nat) (accepted : Bool)
  | accept (sender : node) (value : val) (slot : Nat)
  | accepted (sender : node) (slot : Nat)
  | decide (sender : node) (value : val)
  | heartbeat (sender : node) (epoch : Nat)
  | viewChange (sender : node) (newView : Nat)
  | newView (sender : node) (view : Nat) (log : List val)
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd (BigMsg Nat Nat)
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd (BigMsg Nat Nat)

-- Test 5: Both TransOrd and LawfulEqOrd on same type (tests that both work)
inductive Pair (α : Type) where
  | mk (fst snd : α)
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd (Pair Nat)
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd (Pair Nat)

-- Test 6: Nested inductives (tests that nested instances are generated and used)
structure Msgs (α β γ : Type) where
  a : SmallMsg
  b : MediumMsg α
  c : BigMsg α β
deriving Ord, Std.TransOrd, Std.LawfulEqOrd

#guard_msgs (error, warning, drop all) in
#synth Std.TransOrd (Msgs Nat Nat Nat)
#guard_msgs (error, warning, drop all) in
#synth Std.LawfulEqOrd (Msgs Nat Nat Nat)

end VeilTest.Deriving
