import Lean
open Lean

namespace Veil

abbrev AssertionId := Int

structure AssertionContext where
  /-- Which module is this assertion in? -/
  module : Name
  /-- Which procedure is this assertion in? -/
  procedure : Name
  /-- Which syntax node should be highlighted for this assertion? -/
  stx : Syntax
deriving Inhabited, BEq

structure Assertion where
  id : AssertionId
  /-- The context in which this assertion was created. -/
  ctx : AssertionContext
deriving Inhabited, BEq

/-- A global structure used to keep track of which assertion IDs
correspond to which assertions. -/
structure AssertionEnvironment where
  maxId : AssertionId
  find : Std.HashMap AssertionId Assertion
deriving Inhabited

end Veil
