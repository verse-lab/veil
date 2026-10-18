module

meta import all Veil.Core.UI.Widget.ProgressViewer
meta import VeilTest.TestUtil

meta section

open Veil.ModelChecker Veil.ModelChecker.Concrete

-- Check the grouping path used by the infoview, including numeric runs inside
-- multi-argument and structured labels. Text and action names keep their order.
#eval show IO Unit from do
  let cases : List (List String × List String) := [
    (["10", "2", "1", "0", "23", "11"], ["0", "1", "2", "10", "11", "23"]),
    (["10 1", "1 10", "2 1", "1 2"], ["1 2", "1 10", "2 1", "10 1"]),
    (["(node10, 2)", "(node2, 10)", "(node2, 2)"],
      ["(node2, 2)", "(node2, 10)", "(node10, 2)"]),
    (["β10", "β2", "alpha", ""], ["", "alpha", "β2", "β10"]),
    (["a2", "aa", "a-1", "a10", "a"], ["a", "a-1", "a2", "a10", "aa"]),
    (["02", "2", "002", "10"], ["02", "2", "002", "10"])
  ]
  for (args, expected) in cases do
    let labels := args.map (fun a => s!"Fixture.Label.finish {a}")
    let stats := labels.map (fun name =>
      ({ name, statesGenerated := 3, distinctStates := 2 } : ActionStatDisplay))
    let [group] := groupActionStats stats
      | throw <| IO.userError "expected one action group"
    expect s!"incorrect variant order for {args}" <|
      group.variants.map (·.name) == expected.map (fun a => s!"Fixture.Label.finish {a}")
    expect "sorting must preserve the coverage totals" <|
      group.totalGenerated == args.length * 3 && group.totalDistinct == args.length * 2

#eval show IO Unit from do
  let stats : List ActionStatDisplay := [
    { name := "Fixture.Label.action2 2", statesGenerated := 2, distinctStates := 1 },
    { name := "Fixture.Label.action10 10", statesGenerated := 3, distinctStates := 2 },
    { name := "Fixture.Label.action2 10", statesGenerated := 0, distinctStates := 0 }
  ]
  let groups := groupActionStats stats
  expect "action names must retain their alphabetical order" <|
    groups.map (·.baseName) == ["Fixture.Label.action10", "Fixture.Label.action2"]
  expect "empty coverage must remain empty" (groupActionStats []).isEmpty
