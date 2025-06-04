import Lean
import Veil.Model.Specifications

open Lean

/-! # DSL Environment Extensions -/

def _root_.Lean.EnvExtension.set (ext : EnvExtension σ) (s : σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

def _root_.Lean.EnvExtension.modify (ext : EnvExtension σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

/-- Auxiliary structure to store the transition system objects. This is
per-file temporary state. -/
structure LocalSpecificationCtx where
  spec : ModuleSpecification
  /-- base name of the State type; set when `#gen_state` runs -/
  stateBaseName: Option Name
  /-- keeps track of isolates in this specification -/
  isolates: IsolatesInfo
  /-- established invariant clauses; set on `@[invProof]` label -/
  establishedClauses : List Name := []
deriving Inhabited

def _root_.Lean.SimpleScopedEnvExtension.getIsolates (ext : SimpleScopedEnvExtension LocalSpecificationCtx LocalSpecificationCtx)
  [Monad m] [MonadEnv m] : m IsolatesInfo := do
  return (ext.getState (<- getEnv)).isolates

def _root_.Lean.SimpleScopedEnvExtension.modifyIsolates
  (ext : SimpleScopedEnvExtension LocalSpecificationCtx LocalSpecificationCtx) (s : IsolatesInfo -> IsolatesInfo)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · (fun ctx => { ctx with isolates := s ctx.isolates }))

abbrev GlobalSpecificationCtx := Std.HashMap Name LocalSpecificationCtx

initialize localSpecCtx : SimpleScopedEnvExtension LocalSpecificationCtx LocalSpecificationCtx ←
  registerSimpleScopedEnvExtension {
    initial := default
    addEntry := fun _ s' => s'
  }

initialize globalSpecCtx :
  SimpleScopedEnvExtension (Name × LocalSpecificationCtx) GlobalSpecificationCtx <-
  registerSimpleScopedEnvExtension {
    initial := ∅
    addEntry := fun s (n, thm) => s.insert n thm
  }

structure AssertCtx where
  maxId : Nat
  map   : Std.HashMap Nat Syntax
deriving Inhabited

initialize assertsCtx :
  SimpleScopedEnvExtension Syntax AssertCtx <-
  registerSimpleScopedEnvExtension {
    initial := { maxId := 0, map := ∅ }
    addEntry := fun s stx => { s with maxId := s.maxId + 1, map := s.map.insert s.maxId stx }
  }

/-- Record the local specification in the global specification context. -/
def registerModuleSpecification : AttrM Unit := do
  let lctx := <- localSpecCtx.get
  let n := lctx.spec.name
  if (← globalSpecCtx.get).contains n then
    throwError "Specification {n} has already been declared"
  trace[veil] "Globally declaring specification {n}"
  globalSpecCtx.add (n, lctx)
