module

public import ProofWidgets.Component.RefreshComponent


/-!
Veil used to vendor `RefreshComponent`. ProofWidgets now provides the component
directly, so this module remains as a compatibility import for Veil modules, with what Veil's
uses of the component share.
-/

public meta section

namespace Veil
open Lean ProofWidgets

/-- `html`, which displays a `RefreshComponent`, under a React key that differs each time this runs,
also in another process. A `RefreshComponent` follows a new computation only when it gets a new RPC
reference, but the RPC references of a file are numbered from zero again when the file restarts, so
the component on display would keep showing the computation of the previous elaboration. The key
makes the infoview display a new component instead. -/
def keyedPerElaboration (html : Html) : BaseIO Html := do
  return .element "div" #[("key", toJson (toString (← IO.monoNanosNow)))] #[html]

end Veil
