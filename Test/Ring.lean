import Veil

veil module Ring

type node

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader (n : node)
relation pending : node → node → Prop
function leader_of : node → Nat

immutable individual flag : Prop

#gen_state

-- after_init {
--   leader N := False
--   pending M N := False
-- }

action send (n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

  require ∀ Q, n ≠ Q
  -- require flag
  pending n next := True
}

end Ring
