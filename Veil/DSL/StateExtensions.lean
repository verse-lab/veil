import Lean
import Veil.DSL.Specifications

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
  /-- established invariant clauses; set on `@[invProof]` label -/
  establishedClauses : List Name := []
deriving Inhabited

abbrev GlobalSpecificationCtx := Std.HashMap Name ModuleSpecification

initialize localIsolates : SimpleScopedEnvExtension IsolatesInfo IsolatesInfo <-
  registerSimpleScopedEnvExtension {
    initial := default
    addEntry := fun s _ => s
  }

initialize localSpecCtx : SimpleScopedEnvExtension LocalSpecificationCtx LocalSpecificationCtx ←
  registerSimpleScopedEnvExtension {
    initial := default
    addEntry := fun _ s' => s'
  }


initialize globalSpecCtx :
  SimpleScopedEnvExtension (Name × ModuleSpecification) GlobalSpecificationCtx <-
  registerSimpleScopedEnvExtension {
    initial := ∅
    addEntry := fun s (n, thm) => s.insert n thm
  }

/-- Record the given specification in the global specification context. -/
def registerModuleSpecification (spec : ModuleSpecification) : AttrM Unit := do
  let n := spec.name
  if (← globalSpecCtx.get).contains n then
    throwError "Specification {n} has already been declared"
  trace[dsl] "Globally declaring specification {n}"
  -- stsStateGlobalExt.modify (fun s => s.insert n spec)
  globalSpecCtx.add (n, spec)
