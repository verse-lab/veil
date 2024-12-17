import LeanSts.DSL.SpecLang
import LeanSts.DSL.Check
import LeanSts.DSL.Trace

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp, safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next
