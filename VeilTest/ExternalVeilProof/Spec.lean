import Veil

veil module ExternalVeilProof

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

end ExternalVeilProof
