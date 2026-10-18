module

public import Veil

/-! Model checkers for the tests of the VS Code extension. `npm test` builds them with
`lake env lean --json`, from the root of the repository. -/

veil module RunnerFixture

type node
type NodeSet
instantiate nodeSet : TSet node NodeSet

individual finished : NodeSet

#gen_state

after_init {
  finished := nodeSet.empty
}

action finish (n : node) {
  require ¬ nodeSet.contains n finished
  finished := nodeSet.insert n finished
}

invariant [bounded] nodeSet.count finished ≤ 32

#gen_spec

#gen_executable

end RunnerFixture

-- Explores the 4 subsets of `Fin 2`
#model_check_build RunnerFixture { node := Fin 2, NodeSet := OrdList _ }

-- Explores the 2^24 subsets of `Fin 24`: long enough to stop it while it runs
#model_check_build RunnerFixture { node := Fin 24, NodeSet := OrdList _ }
