import Veil

veil module EnumTest
enum switch_state = {on, off}
enum one_elem = {a}

type node

individual state : switch_state

#gen_state

after_init {
  state := off
}

action random_switch {
  let s ← pick switch_state
  state := s
}

invariant [all] state = on ∨ state = off
invariant [neq] on ≠ off

#gen_spec


/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  all ... ✅
  neq ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  random_switch
    doesNotThrow ... ✅
    all ... ✅
    neq ... ✅
-/
#guard_msgs in
#check_invariants -- verifies

#guard_msgs(drop info, drop warning) in
sat trace {
  random_switch
}

end EnumTest

-- We encountered a strange bug here with the instances. If we have enums in
-- different namespaces/modules, then basic synthesis of stuff like `#synth BEq
-- Nat` will fail. To fix this, we now use `scoped instance`s everywhere.

veil module EnumTest2

enum one_elem = {a}
individual state : one_elem

#gen_state

after_init {
  state := a
}

action random_switch {
  let s ← pick one_elem
  state := s
}

invariant [all] state = a

#gen_spec

end EnumTest2

veil module EnumNamesInCTIs

-- Tests that CTIs refer to enum symbolic names, rather than the underlying
-- numeric values returned by the SMT solver.

enum EnumA = {nop}
enum EnumB = {a,b}

function req : EnumA → EnumB

after_init {
  pure ()
}

action foo {
  let x ← pick EnumA
  let y ← pick EnumB
  req x := y
}

invariant req T ≠ a

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ❌
      Counterexample (WP):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
        Action: initializer
      Counterexample (TR):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
        Action: initializer
        Post-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
The following set of actions must preserve the invariant and successfully terminate:
  foo
    doesNotThrow ... ✅
    inv_0 ... ❌
      Counterexample (WP):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
      Counterexample (TR):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
        Post-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
-/
#guard_msgs in
#check_invariants

end EnumNamesInCTIs

veil module LargeEnumTest

-- Keep this test narrow: the 240-constructor distinctness axiom is the part
-- that used to expand aggressively before `distinctN`.
enum large_enum = {
  v00, v01, v02, v03, v04, v05, v06, v07, v08, v09,
  v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
  v20, v21, v22, v23, v24, v25, v26, v27, v28, v29,
  v30, v31, v32, v33, v34, v35, v36, v37, v38, v39,
  v40, v41, v42, v43, v44, v45, v46, v47, v48, v49,
  v50, v51, v52, v53, v54, v55, v56, v57, v58, v59,
  v60, v61, v62, v63, v64, v65, v66, v67, v68, v69,
  v70, v71, v72, v73, v74, v75, v76, v77, v78, v79,
  v80, v81, v82, v83, v84, v85, v86, v87, v88, v89,
  v90, v91, v92, v93, v94, v95, v96, v97, v98, v99,
  v100, v101, v102, v103, v104, v105, v106, v107, v108, v109,
  v110, v111, v112, v113, v114, v115, v116, v117, v118, v119,
  v120, v121, v122, v123, v124, v125, v126, v127, v128, v129,
  v130, v131, v132, v133, v134, v135, v136, v137, v138, v139,
  v140, v141, v142, v143, v144, v145, v146, v147, v148, v149,
  v150, v151, v152, v153, v154, v155, v156, v157, v158, v159,
  v160, v161, v162, v163, v164, v165, v166, v167, v168, v169,
  v170, v171, v172, v173, v174, v175, v176, v177, v178, v179,
  v180, v181, v182, v183, v184, v185, v186, v187, v188, v189,
  v190, v191, v192, v193, v194, v195, v196, v197, v198, v199,
  v200, v201, v202, v203, v204, v205, v206, v207, v208, v209,
  v210, v211, v212, v213, v214, v215, v216, v217, v218, v219,
  v220, v221, v222, v223, v224, v225, v226, v227, v228, v229,
  v230, v231, v232, v233, v234, v235, v236, v237, v238, v239
}

individual state : large_enum

#gen_state

after_init {
  state := v00
}

action set_last {
  state := v239
}

invariant [large_distinct] ((v00 ≠ v239 ∧ v00 ≠ v01) ∧ v01 ≠ v02) ∧ (v160 ≠ v194 ∧ v25 ≠ v26)

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  large_distinct ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  set_last
    doesNotThrow ... ✅
    large_distinct ... ✅
-/
#guard_msgs in
#check_invariants

end LargeEnumTest
