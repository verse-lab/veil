module

public import Veil

/-! Model checkers for the tests of the VS Code extension. `npm test` builds them with
`lake env lean --json`, from the root of the repository. -/

veil module RunnerFixture

type node
type NodeSet
instantiate nodeSet : TSet node NodeSet

immutable individual limit : Nat
individual finished : NodeSet

#gen_state

after_init {
  finished := nodeSet.empty
}

action finish (n : node) {
  require ¬ nodeSet.contains n finished
  finished := nodeSet.insert n finished
}

invariant [bounded] nodeSet.count finished ≤ limit

#gen_spec

#gen_executable

end RunnerFixture

-- Explores the 4 subsets of `Fin 2`
#model_check_build RunnerFixture { node := Fin 2, NodeSet := OrdList _ } { limit := 2 }

-- Explores the 2^24 subsets of `Fin 24`: long enough to stop it while it runs
#model_check_build RunnerFixture { node := Fin 24, NodeSet := OrdList _ } { limit := 24 }

-- Violates `bounded` once both nodes have finished
#model_check_build RunnerFixture { node := Fin 2, NodeSet := OrdList _ } { limit := 1 }
