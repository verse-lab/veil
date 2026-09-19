import Veil

namespace CompiledInitializersHelper

-- An imported user's module may itself import the full verification frontend.
initialize order : IO.Ref (Array Nat) ← IO.mkRef #[0]
initialize do
  unless (← order.get) == #[0] do
    throw <| IO.userError "imported initialization ran more than once"
  order.modify (·.push 1)

end CompiledInitializersHelper
