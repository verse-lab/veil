module

public import Veil

-- `ModelCheckBuild.lean` builds model checkers for the modules declared here.

public section

namespace ModelCheckBuildHelper

class Collection (elem repr : Type) where
  empty : repr

@[default_instance] instance : Collection α (Array α) where
  empty := #[]

end ModelCheckBuildHelper

-- `ModelCheckBuild.lean` needs no `open` to resolve `Collection` in the constraint below
open ModelCheckBuildHelper

veil module CheckedElsewhere

type node
type NodeSet
type Buffer
enum Phase = { idle, busy }
instantiate nodeSet : TSet node NodeSet
instantiate buffer : Collection node Buffer

immutable individual limit : Nat
individual phase : Phase
individual finished : NodeSet

#gen_state

after_init {
  phase := idle
  finished := nodeSet.empty
}

action finish (n : node) {
  require phase = idle
  require ¬ nodeSet.contains n finished
  finished := nodeSet.insert n finished
}

invariant [bounded] nodeSet.count finished ≤ limit

#gen_spec

#gen_executable

end CheckedElsewhere

veil module NotExecutable

individual flag : Bool

after_init { flag := false }

action toggle { flag := !flag }

invariant flag = true ∨ flag = false

#gen_spec

end NotExecutable
