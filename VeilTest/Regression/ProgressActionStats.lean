module

public import Veil
public meta import Veil
import all Veil.Core.UI.Widget.ProgressViewer

open Lean Veil Veil.ModelChecker Veil.ModelChecker.Concrete

/-!
Action statistics carry the `Display` of their labels, and the progress panel groups them by the
label's constructor, which is the action: each label of an action shows its arguments as a trace
shows them. An action whose labels generated no state is never enabled. A label that is not a
constructor is an action of its own.
-/

veil module ProgressActionStats

individual x : Bool

#gen_state

after_init {
  x := false
}

action flip {
  x := !x
}

action set (v : Bool) {
  x := v
}

invariant true

#gen_spec

end ProgressActionStats

/--
info: flip 0/0: [] 0/0
set 2/1: [v=false] 0/0, [v=true] 2/1
never enabled: [flip]
step 1 1/1: [] 1/1
-/
#guard_msgs in
#eval do
  -- An action with its states generated/distinct, then each of its labels: arguments and counts
  let describe (g : ActionGroup) : String :=
    let variants := g.variants.map fun ((args, st) : String × ActionStatDisplay) =>
      s!"[{args}] {st.statesGenerated}/{st.distinctStates}"
    s!"{g.baseName} {g.totalGenerated}/{g.totalDistinct}: {", ".intercalate variants}"
  -- The statistics that the model checker keeps for the module's labels
  let s := LabelTable.replicate (κ := ProgressActionStats.Label) (default : ActionStat)
  let s := LabelTable.modify (ProgressActionStats.Label.set true) (ActionStat.increment true) s
  let s := LabelTable.modify (ProgressActionStats.Label.set true) (ActionStat.increment false) s
  let groups := groupActionStats (ActionStatDisplay.ofTable (κ := ProgressActionStats.Label) s)
  groups.forM fun g => IO.println (describe g)
  IO.println s!"never enabled: {getNeverEnabledActions groups ["flip", "set"]}"
  (groupActionStats [{ statesGenerated := 1, distinctStates := 1, label := .str "step 1" }]).forM
    fun g => IO.println (describe g)
