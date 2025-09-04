import Lean
import Veil.Frontend.DSL.Module.Representation
open Lean

namespace Veil

structure VCMetadata where
  baseParams : Array Parameter
  extraParams : Array Parameter
  /-- The declarations that this VC depends on. -/
  stmtDerivedFrom : Std.HashSet Name
deriving Inhabited

end Veil
