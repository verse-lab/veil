module

public meta import Veil.Core.Tools.Synthesizer.Structure

/-! Laws of the clause layer of `#synthesize_invariants`, on a two-node Ring
state: evaluation of a structure's diagram and of its blocking clause,
subsumption up to variable renaming, and generalization by dropping literals
of the blocking clause. -/

meta section
open Veil.Synthesizer

def leaderSym : Symbol := { name := `leader, argSorts := #[`node] }
def pendingSym : Symbol := { name := `pending, argSorts := #[`node, `node] }
def leSym : Symbol := { name := `le, origin := .field `tot, argSorts := #[`node, `node] }

/-- The literal `f args`. -/
def pos (f : Symbol) (args : Array Arg) : Literal := { positive := true, atom := .rel f args }
/-- The literal `¬ f args`. -/
def neg (f : Symbol) (args : Array Arg) : Literal := { positive := false, atom := .rel f args }

/-- The order of two nodes, `0 ≤ 1`. -/
def le2 : Array (Array Nat) := #[#[0,0], #[0,1], #[1,1]]

/-- leader = {1}, pending = everything, le = {(0,0), (0,1), (1,1)}. -/
def st0 : FinStructure :=
  { sorts := #[(`node, 2)],
    rels := #[(leaderSym, #[#[1]]), (pendingSym, #[#[0,0], #[0,1], #[1,0], #[1,1]]), (leSym, le2)] }

/-- No leader and no messages: contains no copy of `st0`. -/
def stEmpty : FinStructure :=
  { sorts := #[(`node, 2)], rels := #[(leaderSym, #[]), (pendingSym, #[]), (leSym, le2)] }

/-- Three nodes, containing `st0` as the substructure on nodes {0, 1}. -/
def stBig : FinStructure :=
  { sorts := #[(`node, 3)],
    rels := #[(leaderSym, #[#[1]]), (pendingSym, #[#[0,0], #[0,1], #[1,0], #[1,1], #[2,2]]),
              (leSym, #[#[0,0], #[0,1], #[1,1], #[0,2], #[1,2], #[2,2]])] }

/-- One node, which is the leader: too small to contain `st0`. -/
def stOne : FinStructure :=
  { sorts := #[(`node, 1)], rels := #[(leaderSym, #[#[0]]), (pendingSym, #[]), (leSym, #[#[0,0]])] }

-- Evaluation: a structure satisfies its own diagram and violates its blocking
-- clause, which excludes exactly the structures containing a copy of it.
#guard st0.modelsExistential (st0.elements.map (·.1)) st0.diagramLiterals
#guard !st0.models st0.negatedDiagram
#guard !stBig.models st0.negatedDiagram
#guard stEmpty.models st0.negatedDiagram
#guard stOne.models st0.negatedDiagram

-- Subsumption up to renaming: `∀ x0 x1, ¬ leader x0 ∨ le x1 x0` subsumes
-- `∀ x0 x1, ¬ leader x1 ∨ ¬ pending x0 x1 ∨ le x0 x1` and not the reverse; a
-- non-injective renaming takes "no messages" to "no self-messages".
def leaderGreatest : Clause :=
  { vars := #[`node, `node], lits := #[neg leaderSym #[0], pos leSym #[1, 0]] }
def leaderGreatestWeak : Clause :=
  { vars := #[`node, `node], lits := #[neg leaderSym #[1], neg pendingSym #[0, 1], pos leSym #[0, 1]] }
def noMessages : Clause := { vars := #[`node, `node], lits := #[neg pendingSym #[0, 1]] }
def noSelfMessages : Clause := { vars := #[`node], lits := #[neg pendingSym #[0, 0]] }
#guard leaderGreatest.subsumes leaderGreatestWeak && !leaderGreatestWeak.subsumes leaderGreatest
#guard noMessages.subsumes noSelfMessages && !noSelfMessages.subsumes noMessages
#guard Clause.removeSubsumed id #[leaderGreatestWeak, noSelfMessages, leaderGreatest, noMessages] ==
  #[leaderGreatest, noMessages]

-- Generalization: any literals dropped from the blocking clause leave a
-- clause that still excludes `st0`, subsumes the blocking clause, and
-- excludes more: keeping only `¬ leader x1` gives `∀ x0, ¬ leader x0`, which
-- also excludes the one-node state.
def keepOnly (c : Clause) (l : Literal) : Clause := c.restrict (c.lits[·]! == l)
def noLeader : Clause := keepOnly st0.negatedDiagram (neg leaderSym #[1])
#guard noLeader == { vars := #[`node], lits := #[neg leaderSym #[0]] }
#guard (List.range st0.negatedDiagram.lits.size).all fun i ↦
  !st0.models (st0.negatedDiagram.restrict (· != i))
#guard !st0.models noLeader && noLeader.subsumes st0.negatedDiagram
#guard !stOne.models noLeader

end
