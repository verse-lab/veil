module

public import VeilTest.Regression.ModuleSystemHelper
public meta import VeilTest.Regression.ModuleSystemHelper

open scoped ExportedModel

-- Generated structures and ordinary definitions within a Veil model retain
-- their usable public API and transparent bodies when imported.
example : ExportedModel.initial.flag = false := rfl

#guard ExportedModel.runToggle == [.success () { flag := true }]

-- Importers can use both symbolic and executable definitions from a spec that ran no checks.
example := @ExportedModel.toggle.ext.wp
example := @ExportedModel.toggle.ext.tr
noncomputable example := @ExportedModel.relationalTransitionSystem
example := @ExportedModel.visitsFlag
example := @ExportedModel.visitsFlag.ast
