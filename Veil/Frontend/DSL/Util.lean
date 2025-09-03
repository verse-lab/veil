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

def toDoName (n : Name) := Name.append n `do

def toActName (n : Name) : Mode → Name := fun
  | Mode.internal => n
  | Mode.external => Name.append n `ext

def toExtName (n : Name) := toActName n Mode.external

def toActIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toActName id.getId mode


end Veil
