module

public import Lean.Data.Name

public section

namespace Veil

/-- Stable names for utility-generated implementation details. Keep the generator family,
fully qualified input declaration, and helper role under a Veil-owned namespace rather than
adding library-specific helpers to the input declaration's namespace. -/
def generatedName (family owner role : Lean.Name) : Lean.Name :=
  `Veil.Generated ++ family ++ owner ++ role

end Veil
