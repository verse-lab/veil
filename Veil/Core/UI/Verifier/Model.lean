import Lean
import ProofWidgets
import Smt
open Lean

namespace Smt

def ModelContext.toExprWithCtx (ctx : ModelContext) (expr : Expr) : ProofWidgets.ExprWithCtx :=
  {
    ci := ctx.ci
    lctx := ctx.lctx
    linsts := ctx.linsts
    expr := expr
  }

/-- Check if the given `Expr` (which is assumed to be a `fvar`) can be resolved
in the given `ModelContext`. This is used to filter out fvars that might show
up in the returned model, but were not present in the original Lean goal sent
to SMT. -/
def ModelContext.containsFVar (ctx : ModelContext) (fvar : Expr) : MetaM Bool := do
  let ectx := ctx.toExprWithCtx fvar
  ectx.runMetaM (fun e => return (← getLCtx).containsFVar e)

end Smt

namespace Veil

open ProofWidgets Jsx in
/-- Render a table row with two columns: an interactive expression and interactive code.

Parameters:
- `ctx`: Model context for expression conversion
- `leftExpr`: Expression for the left column (rendered as InteractiveExpr)
- `rightExpr`: Expression for the right column (rendered as InteractiveCode) -/
private def renderRow [Monad m] [MonadLiftT BaseIO m] [MonadLiftT MetaM m]
    (ctx : Smt.ModelContext) (leftExpr rightExpr : Expr) : m (Option Html) := do
  if !(← ctx.containsFVar leftExpr) then
    return none
  let rightFmt ← Widget.ppExprTagged rightExpr
  return <tr>
    <td><InteractiveExpr expr={← Server.WithRpcRef.mk (ctx.toExprWithCtx leftExpr)} /></td>
    <td><InteractiveCode fmt={rightFmt} /></td>
  </tr>

open ProofWidgets Jsx in
/-- Render a section (header + rows) for an SMT model table.

Parameters:
- `title`: Section title (e.g., "Sorts", "Values")
- `data`: Array of data pairs to render
- `headers`: Pair of column headers
- `ctx`: Model context for expression conversion

Returns an array containing the section header and rows, or empty array if data is empty. -/
private def renderSection [Monad m] [MonadLiftT BaseIO m] [MonadLiftT MetaM m]
  (data : Array (Expr × Expr)) (headers : String × String)
  (ctx : Smt.ModelContext) : m (Array Html) := do
  if data.isEmpty then
    return #[]
  let rowsOpt ← data.mapM fun (leftExpr, rightExpr) => renderRow ctx leftExpr rightExpr
  let rows := rowsOpt.filterMap id
  let header := <thead>
    <tr>
      <th className="counterexample-column-header">{.text headers.1}</th>
      <th className="counterexample-column-header">{.text headers.2}</th>
    </tr>
  </thead>
  let tbody := <tbody>{...rows}</tbody>
  return #[header, tbody]

open ProofWidgets Jsx in
/-- Render an SMT model as interactive HTML.

Displays sorts (universe interpretations) and values (constant assignments)
in a structured table format using `InteractiveCode` for interactive expression browsing.

Returns an empty model message if both `sorts` and `values` are empty. -/
def renderSmtModel [Monad m] [MonadLiftT BaseIO m] [MonadLiftT MetaM m] (model : Smt.Model) : m Html := do
  -- Handle empty model case
  if model.isEmpty then
    return <div className="font-code">
      <span>{.text "Empty model"}</span>
    </div>

  -- Build table sections
  let mut tableContent := #[]

  -- Add sorts section if non-empty
  let sortsSection ← renderSection model.sorts ("Sort", "Cardinality") model.ctx
  tableContent := tableContent ++ sortsSection

  -- Add values section if non-empty
  let valuesSection ← renderSection model.values ("Constant", "Value") model.ctx
  tableContent := tableContent ++ valuesSection

  -- Combine into single table
  return <div className="font-code">
    <table>
      {...tableContent}
    </table>
  </div>

end Veil
