module

public meta import Lean

public meta section
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

/-- Source location info for an assertion, used to enrich model checker output. -/
structure AssertionSourceInfo where
  moduleName : Name
  procedureName : Name
  line : Nat
  column : Nat
deriving Inhabited, ToJson

/-- Extract source info for all assertions from the assertion environment.
This must be called during elaboration when FileMap is available. -/
def extractAssertionSources (actx : AssertionEnvironment) (fileMap : FileMap) (moduleName? : Option Name := none)
    : Std.HashMap AssertionId AssertionSourceInfo :=
  actx.find.fold (init := {}) fun acc id assertion => Id.run do
    let ctx := assertion.ctx
    if moduleName?.any (· != ctx.module) then return acc
    let (line, column) := match ctx.stx.getPos? with
      | some pos =>
        let position := fileMap.toPosition pos
        (position.line, position.column)
      | none => (0, 0)
    return acc.insert id { moduleName := ctx.module, procedureName := ctx.procedure, line, column }

end Veil
