module

public import Veil

veil module ImportedActionName
individual doneFlag : Bool
after_init { doneFlag := false }
-- The model action shares its name with Lean's Add type class.
action Add { doneFlag := false }
invariant [off] ¬ doneFlag
#gen_spec
end ImportedActionName
