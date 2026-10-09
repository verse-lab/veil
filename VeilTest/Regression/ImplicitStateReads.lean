module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
# Regression: state reads introduced by default arguments and elaborators

Default-argument tactics and term elaborators can synthesize a
field reference absent from the caller's syntax. After `x := 42`, these reads
must return 42, rather than the stale initial value 7. They must also work
when no earlier statement has bound a view of the field.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

-- The tactic is stored in the function type and runs only when the caller
-- omits `value`. Its syntax is absent from the calling statement.
public def implicitStateReadDefault (value : Nat := by exact x) : Nat := value

-- `by_elab` is a Lean builtin, but can run arbitrary elaboration code.
public meta def elabImplicitStateRead : Lean.Elab.Term.TermElabM Lean.Expr :=
  Lean.Elab.Term.elabTerm (Lean.mkIdent `x) (some (Lean.mkConst ``Nat))

-- A custom identifier elaborator synthesizes the field reference.
@[term_elab ident]
public meta def elabImplicitStateReadIdent : Lean.Elab.Term.TermElab := fun stx ty? => do
  unless stx.getId == `implicit_state_read do Lean.Elab.throwUnsupportedSyntax
  Lean.Elab.Term.elabTerm (Lean.mkIdent `x) ty?

-- Field lookup also works in an elaborator declared in the `Lean` namespace.
namespace Lean
elab "implicit_state_read_in_lean" : term =>
  Lean.Elab.Term.elabTerm (Lean.mkIdent `x) (some (Lean.mkConst ``Nat))
end Lean

veil module ImplicitStateReads

individual x : Nat
individual y : Nat

#gen_state

def initial : State FieldConcreteType := { x := 7, y := 0 }

-- Check each implicit read both after a write and as the first statement.
macro "implicit_read_case " id:ident " := " rhs:term : command => do
  let afterWrite := Lean.mkIdent (id.getId.appendAfter "_after_write")
  let firstRead := Lean.mkIdent (id.getId.appendAfter "_first")
  let afterResult := Lean.mkIdent (id.getId.appendAfter "_after_result")
  let firstResult := Lean.mkIdent (id.getId.appendAfter "_first_result")
  `(section
    procedure $afterWrite { x := 42; return $rhs }
    procedure $firstRead { return $rhs }
    def $afterResult := __veil_exec_action% {} {} initial $afterWrite
    def $firstResult := __veil_exec_action% {} {} initial $firstRead
    #guard exactlyOneSuccess $afterResult fun value state =>
      value == 42 && state == { initial with x := 42 }
    #guard exactlyOneSuccess $firstResult fun value state =>
      value == 7 && state == initial
    end)

implicit_read_case default_argument := implicitStateReadDefault
implicit_read_case named_elaboration := (by_elab elabImplicitStateRead)
-- The quoted `x` is data until `by_elab` interprets it as a field reference.
implicit_read_case inline_elaboration :=
  (by_elab Lean.Elab.Term.elabTerm (Lean.mkIdent `x) none)
implicit_read_case identifier_elaboration := implicit_state_read
implicit_read_case namespaced_elaboration := implicit_state_read_in_lean

-- An implicit read must also see the write when used to update another field.
procedure copy_default_argument { x := 42; y := implicitStateReadDefault }
def copyResult := __veil_exec_action% {} {} initial copy_default_argument
#guard exactlyOneSuccess copyResult fun _ state => state == { x := 42, y := 42 }

-- Check both assertion outcomes to distinguish fresh reads from stale ones.
procedure assert_current_value { x := 42; assert implicitStateReadDefault = 42 }
def assertionResult := __veil_exec_action% {} {} initial assert_current_value
#guard exactlyOneSuccess assertionResult fun _ state => state == { initial with x := 42 }

procedure assert_stale_value { x := 42; assert implicitStateReadDefault = 7 }
def staleAssertionResult := __veil_exec_action% {} {} initial assert_stale_value
#guard staleAssertionResult.length == 1
#guard hasAssertionFailure staleAssertionResult fun _ state =>
  state == { initial with x := 42 }

end ImplicitStateReads
