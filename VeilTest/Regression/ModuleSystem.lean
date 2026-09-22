module

public import VeilTest.Regression.ModuleSystemHelper
public meta import VeilTest.Regression.ModuleSystemHelper

open scoped ExportedModel

-- Generated structures and ordinary definitions within a Veil model retain
-- their usable public API and transparent bodies when imported.
example : ExportedModel.initial.flag = false := rfl

#guard ExportedModel.runToggle == [.success () { flag := true }]
