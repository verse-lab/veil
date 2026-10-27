module

public import Veil
public import VeilTest.Regression.ModelCheckBuildHelper
meta import Lean

/-! `#mc_config` applies the defaults of `veil module` only for its own elaboration. -/

-- Keep distinct surrounding values to check that all three options are restored.
set_option maxRecDepth 2048
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 128

-- Equality for the nested sets exceeds Lean's default instance-size limit. A config file
-- importing the module needs Veil's defaults just as a check inside `veil module` does.
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere
  { node := OrdList (OrdList (OrdList (Fin 1))), NodeSet := OrdList _, Buffer := Array _ }
  { limit := 1 }

open Lean Elab Command in
run_cmd do
  let opts ← getOptions
  unless maxRecDepth.get opts == 2048 && maxHeartbeats.get opts == 700000 &&
      Meta.synthInstance.maxSize.get opts == 128 do
    throwError "#mc_config changed the surrounding elaboration options"
