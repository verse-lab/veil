import ProofWidgets.Component.Basic
import ProofWidgets.Compat

namespace ProofWidgets
open Lean

/-! # Model Checker View Component

This component provides a flexible view for model checker output,
capable of parsing structured text into interactive state displays.
-/

/-- Props for the ModelCheckerView component -/
structure ModelCheckerViewProps where
  /-- Raw text output from model checker -/
  -- text : String
  trace : Json
  /-- Layout orientation: "vertical" or "horizontal" -/
  layout : String := "vertical"
  deriving Server.RpcEncodable

/-- Model Checker View visualization component.

This component parses structured text output from model checkers
and displays it as interactive state cards. The text should contain
states formatted as:

```
index: 0
field1: value1
field2: value2

index: 1
field1: value3
field2: value4
```
-/
@[widget_module]
def ModelCheckerView : Component ModelCheckerViewProps where
  javascript := include_str "."  / "frontend.js"

end ProofWidgets
