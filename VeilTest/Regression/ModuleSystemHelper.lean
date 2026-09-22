module

public import Veil

-- A model's generated API must be usable by importing files without a public
-- section or expose annotations, including matchers and ghost default arguments.
veil module ExportedModel

individual flag : Bool
ghost relation enabled := ¬flag

after_init { flag := false }

action toggle {
  require enabled
  flag := match flag with
    | true => false
    | false => true
}

invariant flag = true ∨ enabled

def initial : State FieldConcreteType := { flag := false }
def runToggle := __veil_exec_action% {} {} initial toggle

end ExportedModel

-- The defaults set by `veil module` must not escape its namespace.
def privateAfterModule := 42

run_cmd do
  if (← Lean.getEnv).contains `privateAfterModule then
    throwError "veil module leaked public visibility beyond its end"
