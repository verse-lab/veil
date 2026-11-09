module

public meta import ProofWidgets.Component.Basic

public meta section

namespace Veil
open Lean

/-- Data passed to a visualizer for one displayed state, regardless of the witness's producer.
Fields and theory are keyed by name; their values use Veil's usual `Display` encoding.
`previous` is absent at the beginning of the witness. -/
structure StateViewProps where
  fields : Json
  previous : Option Json
  theory : Json
  instantiation : Json
  transition : Option Json
  showRemovals : Bool
  hiddenFields : Array String
  deriving Server.RpcEncodable

/-- Optional display fields computed from the actual Lean instances of a concrete check.
These supplement the displayed theory for the state visualizer. -/
class StateViewTheory {ι : Type u} (inst : ι) where
  fields : Json

/-- Data captured at the checking command. The extra theory is only needed if it shows a witness. -/
structure ConcreteVisualization where
  instantiation : Json := .null
  extraTheory : Thunk Json := Thunk.mk fun _ => .null

/-- A standard Lean widget, loaded by hash at the checking command's position. -/
structure StateVisualizer where
  hash : String
  exportName : String
  deriving Inhabited, Server.RpcEncodable

private initialize stateVisualizerExt :
    SimplePersistentEnvExtension (Name × StateVisualizer) (Std.HashMap Name StateVisualizer) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun es => es.foldl (init := {}) fun s entries =>
      entries.foldl (fun s (n, v) => s.insert n v) s
  }

def getStateVisualizer? [Monad m] [MonadEnv m] (mod : Name) : m (Option StateVisualizer) :=
  return (stateVisualizerExt.getState (← getEnv))[mod]?

def registerStateVisualizer [MonadEnv m] (mod : Name)
    (component : ProofWidgets.Component StateViewProps) : m Unit :=
  modifyEnv (stateVisualizerExt.addEntry ·
    (mod, { hash := toString (hash component.javascript), exportName := component.export }))

end Veil
