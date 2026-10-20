module

public import Veil

veil module TraceBindingsErrors

type node

relation visited : node → Bool

#gen_state

after_init {
  visited N := false
}

action visit (n : node) {
  visited n := true
}

action visit_pair (n m : node) {
  visited n := true
  visited m := true
}

invariant True

#gen_spec

/-- error: action 'visit_pair' expects 2 arguments, but 1 were supplied; use '_' for unspecified arguments -/
#guard_msgs in
sat trace (n : node) {
  visit_pair n
}

/-- error: action 'visit' expects 1 arguments, but 2 were supplied; use '_' for unspecified arguments -/
#guard_msgs in
sat trace (n m : node) {
  visit n m
}

-- Undeclared names are errors, including uppercase names in action arguments.
/--
error: Verification error
---
error: Unknown identifier `missing`
-/
#guard_msgs in
sat trace {
  visit missing
}

/--
error: Verification error
---
error: Unknown identifier `N`
-/
#guard_msgs in
sat trace {
  visit N
}

/--
error: Verification error
---
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  node
-/
#guard_msgs in
sat trace {
  visit true
}

/-- error: duplicate trace binding 'n' -/
#guard_msgs in
sat trace (n n : node) {
  visit n
}

/-- error: trace binding 'visited' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (visited : node) {
  visit visited
}

/-- error: trace binding 'node' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (node : node) {
  visit node
}

/-- error: trace binding 'st0' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (st0 : node) {
  visit st0
}

-- Anonymous and untyped header parameters are rejected by the parser, before
-- command elaboration (and hence before #guard_msgs can capture diagnostics).
run_cmd do
  let env ← Lean.getEnv
  for source in ["sat trace (_ : node) { visit _ }", "sat trace (n) { visit n }"] do
    match Lean.Parser.runParserCategory env `command source with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted an invalid trace header: {source}"

-- A successful trace must not add its witnesses to the next query's scope.
#guard_msgs(drop info, drop warning) in
sat trace (localWitness : node) {
  visit localWitness
}

/--
error: Verification error
---
error: Unknown identifier `localWitness`
-/
#guard_msgs in
sat trace {
  visit localWitness
}

end TraceBindingsErrors
