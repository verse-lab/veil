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

-- TODO These names should be put together with the other names
def toExtName (n : Name) := toActName n Mode.external
def toExtractedName (n : Name) := n ++ `extracted

def toActIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toActName id.getId mode

def toWpName (n : Name) : Name := n ++ `wp
def toWpEqName (n : Name) : Name := n ++ `wp_eq
def toWpSuccName (n : Name) : Name := n ++ `wpSucc
def toWpSuccEqName (n : Name) : Name := n ++ `wpSucc_eq
def toWpExName (n : Name) : Name := n ++ `wpEx
def toWpExEqName (n : Name) : Name := n ++ `wpEx_eq

def toTransitionName (n : Name) : Name := n ++ `tr
def toTransitionEqName (n : Name) : Name := n ++ `tr_eq_wpSucc
def toDerivedEqName (n : Name) : Name := n ++ `derived_eq
def toExQuantifiedTransitionName (n : Name) : Name := n ++ `exTr
def toExQuantifiedTransitionEqName (n : Name) : Name := n ++ `exTr_eq

-- def toEndToEndEqName (n : Name) : Name := n ++ `twoState_eq

def toWpLocalEqName (n : Name) : Name := n ++ `wp_local_eq
def toLocalAbstractEqName (n : Name) : Name := n ++ `local_abstract_eq

def toCoreSimplifiedName (n : Name) : Name := n ++ `core_simplified
def toCoreSimplifiedEqName (n : Name) : Name := n ++ `core_simplified_eq

def toTransitionAbstractName (n : Name) : Name := n ++ `tr_abstract

end Veil
