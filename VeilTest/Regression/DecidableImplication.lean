import Veil

veil module ImplicationElaborationFail

type node

individual round : Nat
function crashed (n : node) : Bool
function crashedInRound (n : node) : Nat
ghost relation crashedInThisRound (n : node) := (crashed n ∧ crashedInRound n = round)

after_init {
  round := 0
  crashed N := false
  crashedInRound N := 0
}

action advanceRound {
  let delivery : (node → node → Bool) :|
    (∀ (sender : node), (¬ crashedInThisRound sender) → (∀ (receiver : node), delivery sender receiver))

}

#guard_msgs(drop warning) in
#gen_spec

end ImplicationElaborationFail
