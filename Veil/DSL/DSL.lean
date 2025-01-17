import Veil.DSL.SpecLang
import Veil.DSL.Check
import Veil.DSL.Trace

attribute [initSimp, actSimp] RelationalTransitionSystem.init
attribute [initSimp, invSimp] RelationalTransitionSystem.assumptions
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next

attribute [invSimp, safeSimp, initSimp, actSimp]
  RelationalTransitionSystem.invSafe RelationalTransitionSystem.invInit
  RelationalTransitionSystem.invConsecution
  RelationalTransitionSystem.invInductive
