import Veil.DSL.SpecLang
import Veil.DSL.Check
import Veil.DSL.Trace

attribute [initSimp, actSimp] RelationalTransitionSystem.init
attribute [initSimp, invSimp] RelationalTransitionSystem.assumptions
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next

attribute [initSimp, actSimp] AxiomaticTransitionSystem.init
attribute [initSimp, invSimp] AxiomaticTransitionSystem.assumptions
attribute [invSimp] AxiomaticTransitionSystem.inv
attribute [invSimp, safeSimp] AxiomaticTransitionSystem.safe
attribute [actSimp] AxiomaticTransitionSystem.next

attribute [invSimp, safeSimp, initSimp, actSimp]
  RelationalTransitionSystem.invSafe AxiomaticTransitionSystem.invSafe
  RelationalTransitionSystem.invInit AxiomaticTransitionSystem.invInit
  RelationalTransitionSystem.invConsecution AxiomaticTransitionSystem.invConsecution
  RelationalTransitionSystem.invInductive AxiomaticTransitionSystem.invInductive
