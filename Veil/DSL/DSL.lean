import Veil.DSL.SpecLang
import Veil.DSL.Check
import Veil.DSL.Trace

attribute [initSimp, actSimp] RelationalTransitionSystem.init
attribute [initSimp, invSimp, invSimpLite] RelationalTransitionSystem.assumptions
attribute [invSimp, invSimpLite] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp, invSimpLite] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next

attribute [invSimp, safeSimp, initSimp, actSimp, invSimpLite]
  RelationalTransitionSystem.invSafe RelationalTransitionSystem.invInit
  RelationalTransitionSystem.invConsecution
  RelationalTransitionSystem.invInductive
