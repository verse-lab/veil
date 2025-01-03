import Veil.DSL.SpecLang
import Veil.DSL.Check
import Veil.DSL.Trace

attribute [initSimp] RelationalTransitionSystem.init
attribute [initSimp, invSimp] RelationalTransitionSystem.assumptions
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next
