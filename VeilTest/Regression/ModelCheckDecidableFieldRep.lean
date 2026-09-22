import Veil

veil module ModelCheckDecidableFieldRep

type node
type NodeSet
instantiate nodeSet : TSet node NodeSet

function marked : node → NodeSet

#gen_state

ghost relation available (n : node) :=
  ¬ ∃ owner : node, n ∈ marked owner

after_init {
  marked N := nodeSet.empty
}

-- Regression: model-checker elaboration must synthesize the action's extracted
-- `Decidable` after concrete state fields have been exposed through
-- `FieldRepresentation.get`.
action reserve (owner : node) (requested : NodeSet) {
  require ∀ n : { n // n ∈ requested },
    available n.val ∧ n.val ∈ marked owner
}

invariant [trivial] true

#gen_spec

#model_check interpreted
  { node := Fin 1,
    NodeSet := OrdList (Fin 1) }
  {}
  (maxDepth := 1)
  (sequential := true)

end ModelCheckDecidableFieldRep
