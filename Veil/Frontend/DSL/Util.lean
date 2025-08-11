import Lean
import Veil.Frontend.DSL.Action.Semantics.Definitions

open Lean

namespace Veil

def Mode.stx [Monad m] [MonadQuotation m] : Mode → m Term := fun
  | Mode.internal => `($(mkIdent ``Mode.internal))
  | Mode.external => `($(mkIdent ``Mode.external))

def toActName (n : Name) : Mode → Name := fun
  | Mode.internal => n
  | Mode.external => n ++ `ext

def toActIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toActName id.getId mode


end Veil
