import Lean
import Veil.Frontend.DSL.Action.Semantics.Definitions

open Lean

namespace Veil

def Mode.stx [Monad m] [MonadQuotation m] : Mode → m Term := fun
  | Mode.internal => `($(mkIdent ``Mode.internal))
  | Mode.external => `($(mkIdent ``Mode.external))

def Mode.expr : Mode → Expr := fun
  | Mode.internal => mkConst ``Mode.internal
  | Mode.external => mkConst ``Mode.external

def toDoName (n : Name) := n ++ `do

def toActName (n : Name) : Mode → Name := fun
  | Mode.internal => n
  | Mode.external => n ++ `ext

def toActIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toActName id.getId mode


end Veil
