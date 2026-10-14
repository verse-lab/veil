module

public import Veil

-- CAVA_LTL_Modelchecker/BoolProgs/Programs/BoolProgs_LeaderFilters.thy, `leader_filters` at
-- n=3 (matches `demo_lf_chosen = chose_prog (STR ''LF'') 3` in CAVA_Impl.thy). AFP entry:
-- https://www.isa-afp.org/entries/CAVA_LTL_Modelchecker.html. Actions are 3 copies (i=0,1,2)
-- of `process n i`; the literal-definition comments below are given once, on the i=0 copies.
veil module BoolProgLeaderFilters

individual elected : Bool
individual error : Bool

individual turn0 : Nat
individual turn1 : Nat
individual turn2 : Nat
individual b0 : Bool
individual b1 : Bool
individual b2 : Bool
individual c0 : Bool
individual c1 : Bool
individual c2 : Bool

individual curr0 : Nat
individual curr1 : Nat
individual curr2 : Nat

individual l1_0 : Bool
individual l2_0 : Bool
individual l3_0 : Bool
individual l4_0 : Bool
individual l5_0 : Bool
individual l8_0 : Bool
individual l9_0 : Bool

individual l1_1 : Bool
individual l2_1 : Bool
individual l3_1 : Bool
individual l4_1 : Bool
individual l5_1 : Bool
individual l8_1 : Bool
individual l9_1 : Bool

individual l1_2 : Bool
individual l2_2 : Bool
individual l3_2 : Bool
individual l4_2 : Bool
individual l5_2 : Bool
individual l8_2 : Bool
individual l9_2 : Bool

#gen_state

set_option maxRecDepth 8192

after_init {
  elected := false
  error := false
  turn0 := 0
  turn1 := 0
  turn2 := 0
  b0 := false
  b1 := false
  b2 := false
  c0 := false
  c1 := false
  c2 := false
  curr0 := 0
  curr1 := 0
  curr2 := 0
  l1_0 := true
  l2_0 := false
  l3_0 := false
  l4_0 := false
  l5_0 := false
  l8_0 := false
  l9_0 := false
  l1_1 := true
  l2_1 := false
  l3_1 := false
  l4_1 := false
  l5_1 := false
  l8_1 := false
  l9_1 := false
  l1_2 := true
  l2_2 := false
  l3_2 := false
  l4_2 := false
  l5_2 := false
  l8_2 := false
  l9_2 := false
}

-- L_1[i]: turn[curr[i]] := i+1; L_1[i],L_2[i] := FF,TT
action announce0 {
  require l1_0
  if curr0 = 0 then
    turn0 := 1
  else if curr0 = 1 then
    turn1 := 1
  else
    turn2 := 1
  l1_0 := false
  l2_0 := true
}

-- L_2[i] ∧ ¬b[curr[i]]: L_2[i],L_3[i] := FF,TT
action checkFree0 {
  let free := if curr0 = 0 then ¬b0 else if curr0 = 1 then ¬b1 else ¬b2
  require l2_0 ∧ free
  l2_0 := false
  l3_0 := true
}

-- L_3[i]: b[curr[i]] := TT; L_3[i],L_4[i] := FF,TT
action claim0 {
  require l3_0
  if curr0 = 0 then
    b0 := true
  else if curr0 = 1 then
    b1 := true
  else
    b2 := true
  l3_0 := false
  l4_0 := true
}

-- L_4[i] ∧ turn[curr[i]]=i+1: L_4[i],L_8[i] := FF,TT
action verifyWin0 {
  let tv := if curr0 = 0 then turn0 else if curr0 = 1 then turn1 else turn2
  require l4_0 ∧ tv = 1
  l4_0 := false
  l8_0 := true
}

-- L_4[i] ∧ turn[curr[i]]≠i+1: L_4[i],L_5[i] := FF,TT
action verifyLose0 {
  let tv := if curr0 = 0 then turn0 else if curr0 = 1 then turn1 else turn2
  require l4_0 ∧ tv ≠ 1
  l4_0 := false
  l5_0 := true
}

-- L_5[i]: c[curr[i]],b[curr[i]] := TT,FF; L_5[i] := FF
action retreat0 {
  require l5_0
  if curr0 = 0 then
    c0 := true
    b0 := false
  else if curr0 = 1 then
    c1 := true
    b1 := false
  else
    c2 := true
    b2 := false
  l5_0 := false
}

-- L_8[i] ∧ curr[i]=0: curr[i]++; L_8[i],L_1[i] := FF,TT
action restart0 {
  require l8_0 ∧ curr0 = 0
  curr0 := 1
  l8_0 := false
  l1_0 := true
}

-- L_8[i] ∧ curr[i]≠0 ∧ ¬c[curr[i]]: L_8[i],L_9[i] := FF,TT
action win0 {
  let closed := if curr0 = 1 then c1 else c2
  require l8_0 ∧ curr0 ≠ 0 ∧ ¬closed
  l8_0 := false
  l9_0 := true
}

-- L_8[i] ∧ curr[i]≠0 ∧ c[curr[i]]: curr[i]++; L_8[i],L_1[i] := FF,TT
action advance0 {
  let closed := if curr0 = 1 then c1 else c2
  require l8_0 ∧ curr0 ≠ 0 ∧ closed
  curr0 := curr0 + 1
  l8_0 := false
  l1_0 := true
}

-- L_9[i]: elected,L_9[i] := TT,FF
action declareElected0 {
  require l9_0
  elected := true
  l9_0 := false
}

-- L_9[i] ∧ elected: error,L_9[i] := TT,FF
action declareError0 {
  require l9_0 ∧ elected
  error := true
  l9_0 := false
}

action announce1 {
  require l1_1
  if curr1 = 0 then
    turn0 := 2
  else if curr1 = 1 then
    turn1 := 2
  else
    turn2 := 2
  l1_1 := false
  l2_1 := true
}

action checkFree1 {
  let free := if curr1 = 0 then ¬b0 else if curr1 = 1 then ¬b1 else ¬b2
  require l2_1 ∧ free
  l2_1 := false
  l3_1 := true
}

action claim1 {
  require l3_1
  if curr1 = 0 then
    b0 := true
  else if curr1 = 1 then
    b1 := true
  else
    b2 := true
  l3_1 := false
  l4_1 := true
}

action verifyWin1 {
  let tv := if curr1 = 0 then turn0 else if curr1 = 1 then turn1 else turn2
  require l4_1 ∧ tv = 2
  l4_1 := false
  l8_1 := true
}

action verifyLose1 {
  let tv := if curr1 = 0 then turn0 else if curr1 = 1 then turn1 else turn2
  require l4_1 ∧ tv ≠ 2
  l4_1 := false
  l5_1 := true
}

action retreat1 {
  require l5_1
  if curr1 = 0 then
    c0 := true
    b0 := false
  else if curr1 = 1 then
    c1 := true
    b1 := false
  else
    c2 := true
    b2 := false
  l5_1 := false
}

action restart1 {
  require l8_1 ∧ curr1 = 0
  curr1 := 1
  l8_1 := false
  l1_1 := true
}

action win1 {
  let closed := if curr1 = 1 then c1 else c2
  require l8_1 ∧ curr1 ≠ 0 ∧ ¬closed
  l8_1 := false
  l9_1 := true
}

action advance1 {
  let closed := if curr1 = 1 then c1 else c2
  require l8_1 ∧ curr1 ≠ 0 ∧ closed
  curr1 := curr1 + 1
  l8_1 := false
  l1_1 := true
}

action declareElected1 {
  require l9_1
  elected := true
  l9_1 := false
}

action declareError1 {
  require l9_1 ∧ elected
  error := true
  l9_1 := false
}

action announce2 {
  require l1_2
  if curr2 = 0 then
    turn0 := 3
  else if curr2 = 1 then
    turn1 := 3
  else
    turn2 := 3
  l1_2 := false
  l2_2 := true
}

action checkFree2 {
  let free := if curr2 = 0 then ¬b0 else if curr2 = 1 then ¬b1 else ¬b2
  require l2_2 ∧ free
  l2_2 := false
  l3_2 := true
}

action claim2 {
  require l3_2
  if curr2 = 0 then
    b0 := true
  else if curr2 = 1 then
    b1 := true
  else
    b2 := true
  l3_2 := false
  l4_2 := true
}

action verifyWin2 {
  let tv := if curr2 = 0 then turn0 else if curr2 = 1 then turn1 else turn2
  require l4_2 ∧ tv = 3
  l4_2 := false
  l8_2 := true
}

action verifyLose2 {
  let tv := if curr2 = 0 then turn0 else if curr2 = 1 then turn1 else turn2
  require l4_2 ∧ tv ≠ 3
  l4_2 := false
  l5_2 := true
}

action retreat2 {
  require l5_2
  if curr2 = 0 then
    c0 := true
    b0 := false
  else if curr2 = 1 then
    c1 := true
    b1 := false
  else
    c2 := true
    b2 := false
  l5_2 := false
}

action restart2 {
  require l8_2 ∧ curr2 = 0
  curr2 := 1
  l8_2 := false
  l1_2 := true
}

action win2 {
  let closed := if curr2 = 1 then c1 else c2
  require l8_2 ∧ curr2 ≠ 0 ∧ ¬closed
  l8_2 := false
  l9_2 := true
}

action advance2 {
  let closed := if curr2 = 1 then c1 else c2
  require l8_2 ∧ curr2 ≠ 0 ∧ closed
  curr2 := curr2 + 1
  l8_2 := false
  l1_2 := true
}

action declareElected2 {
  require l9_2
  elected := true
  l9_2 := false
}

action declareError2 {
  require l9_2 ∧ elected
  error := true
  l9_2 := false
}

safety [noError] error = false

-- Same property as the CAVA/Isabelle `demo_leader_filters` binary: F (elected).
temporal [φEventuallyElected] ◇ ⌜ elected = true ⌝

-- Not checked in the corresponding Isabelle demo; holds.
temporal [φNoError] □ ¬ ⌜ error = true ⌝

-- Not checked in the corresponding Isabelle demo; holds.
temporal [φStableElection] ◇ □ ⌜ elected = true ⌝

#gen_spec

-- Checks every `liveness` property above in declaration order, stopping at the first counterexample.
#liveness_check {}

end BoolProgLeaderFilters
