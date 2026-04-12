import Veil
veil module FloodSet

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat                        -- maximum number of crash failures

individual round : Nat                              -- current round number (0 to f+1)
function crashed (n : node) : Bool                  -- has this node crashed?
individual numCrashed : Nat                         -- total number of crashes so far

after_init { pure () }

#guard_msgs in
transition crash (n : node) {
  round < f + 1
  ∧ numCrashed < f
  ∧ ¬ crashed n
  ∧ (∀ N, crashed' N = if N == n then true else crashed N)
  ∧ (numCrashed' = numCrashed + 1)
}
