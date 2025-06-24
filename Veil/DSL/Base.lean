import Veil.Base
import Veil.Model.TransitionSystem

attribute [initSimp, actSimp] RelationalTransitionSystem.init
attribute [initSimp, invSimp, invSimpTopLevel] RelationalTransitionSystem.assumptions
attribute [invSimp, invSimpTopLevel] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp, invSimpTopLevel] RelationalTransitionSystem.safe
attribute [nextSimp, actSimp] RelationalTransitionSystem.next

attribute [invSimp, safeSimp, initSimp, actSimp, invSimpTopLevel]
  RelationalTransitionSystem.invSafe RelationalTransitionSystem.invInit
  RelationalTransitionSystem.invConsecution
  RelationalTransitionSystem.invInductive
