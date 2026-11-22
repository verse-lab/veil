module

public import VeilTest.Regression.ImportedProofs.ActionNameCheck

-- The spec and checker live in two other files. Closing the checking file
-- publishes both forms of its invariant proof for use in this third file.
example := @ImportedActionName.Add_off
example := @ImportedActionName.Add_off_tr
