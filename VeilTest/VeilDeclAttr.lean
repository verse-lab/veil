import Veil

veil module VeilDeclAttrTest

#guard_msgs (error, warning) in
/-- A simple structure -/
@[ext, veil_decl, grind]
structure S (α β : Type) where
  a : α
  b : β

end VeilDeclAttrTest
