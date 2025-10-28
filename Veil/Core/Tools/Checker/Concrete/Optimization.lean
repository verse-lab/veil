import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Perm

instance [Ord α] [Ord β] : Ord (α × β) where
    compare := (fun (a, b) (c, d) =>
    (compare a c).then (compare b d))


instance [Ord α] [Hashable α] : Hashable (Std.TreeSet α) where
  hash s := hash (s.toArray)

instance [BEq α] [Ord α]: BEq (Std.TreeSet α) where
  beq s1 s2 := s1.toArray == s2.toArray

#check cmp
#check Lean.mkIdent ``cmp
#check Std.TreeSet
structure Equivalent (process : Type) (seq_t : Type) (pc_state : Type)
  [Ord process] [Ord seq_t] [Ord pc_state] where
  num : Std.TreeSet (process × seq_t)
  flag : Std.TreeSet process
  unchecked : Std.TreeSet (process × process)
  max : Std.TreeSet (process × seq_t)
  nxt : Std.TreeSet (process × process)
  pc : Std.TreeSet (process × pc_state)
deriving Hashable, BEq

instance [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare (s1.toArray) (s2.toArray)

-- instance [Ord α] [Ord β] : Ord (Std.TreeSet (α × β)) where
--   compare s1 s2 :=
--     compare (s1.toArray) (s2.toArray)

instance [Ord process] [Ord seq_t] [Ord pc_state]
: Ord (Equivalent process seq_t pc_state) where
  compare a b :=
    (compare a.num b.num).then
      ((compare a.flag b.flag).then
        ((compare a.unchecked b.unchecked).then
          ((compare a.max b.max).then
            ((compare a.nxt b.nxt).then
              ((compare a.pc b.pc))))))


def TreeSet.ofList [Ord α] (xs : List α) : Std.TreeSet α :=
  xs.foldl (fun s a => s.insert a) .empty

def mapTreeSet [Ord α ] [Ord β] (f : α → β) (s : Std.TreeSet α)
  : Std.TreeSet β :=
  TreeSet.ofList (s.toList.map f)

def permutateEquivalent [Ord process] [Ord seq_t] [Ord pc_state]
  (e : Equivalent process seq_t pc_state)
  (σ : Equiv.Perm process) : Equivalent process seq_t pc_state :=
{
  e with
  num := mapTreeSet (fun (p, s) => (σ p, s)) e.num,
  flag := mapTreeSet σ e.flag,
  unchecked := mapTreeSet (fun (p1, p2) => (σ p1, σ p2)) e.unchecked,
  max := mapTreeSet (fun (p, s) => (σ p, s)) e.max,
  nxt := mapTreeSet (fun (p1, p2) => (σ p1, σ p2)) e.nxt,
  pc := mapTreeSet (fun (p, st) => (σ p, st)) e.pc
}

class Permutable (α : Type) where
  permute : Equiv.Perm β → α → α
#print LawfulHashable

def permutateEquivalent_ef [Ord process] [Ord seq_t] [Ord pc_state]
  (e : Equivalent process seq_t pc_state)
  (σ : Equiv.Perm process) : Equivalent process seq_t pc_state :=
  -- Return a lexicographically smallest state fingerprint.
  let num' := mapTreeSet (fun (p, s) => (σ p, s)) e.num
  if compare num' e.num == .gt then
    e
  else
    let flag' := mapTreeSet σ e.flag
    if compare flag' e.flag == .gt then
      e
    else
      let unchecked' := mapTreeSet (fun (p1, p2) => (σ p1, σ p2)) e.unchecked
      if compare unchecked' e.unchecked == .gt then
        e
      else
        let max' := mapTreeSet (fun (p, s) => (σ p, s)) e.max
        if compare max' e.max == .gt then
          e
        else
          let nxt' := mapTreeSet (fun (p1, p2) => (σ p1, σ p2)) e.nxt
          if compare nxt' e.nxt == .gt then
            e
          else
            let pc' := mapTreeSet (fun (p, st) => (σ p, st)) e.pc
            if compare pc' e.pc == .gt then
              e
            else
              { num := num',
                flag := flag',
                unchecked := unchecked',
                max := max',
                nxt := nxt',
                pc := pc' }

-- structure Equivalent (process : Type) (seq_t : Type) (pc_state : Type)
--   [Ord process] [Ord seq_t] [Ord pc_state] where
--   num : Std.TreeSet (process × seq_t)
--   flag : Std.TreeSet process
--   unchecked : Std.TreeSet (process × process)
--   max : Std.TreeSet (process × seq_t)
--   nxt : Std.TreeSet (process × process)
--   pc : Std.TreeSet (process × pc_state)
-- deriving Hashable, BEq

def e0 : Equivalent (Fin 3) (Fin 2) (Fin 2) :=
  { num := Std.TreeSet.ofList [(2, 1), (1, 1)] _,
    flag := Std.TreeSet.ofList [0] _,
    unchecked := Std.TreeSet.ofList [(0, 1)] _,
    max := Std.TreeSet.ofList [(0, 0), (1, 1)] _,
    nxt := Std.TreeSet.ofList [(2, 2), (0, 1)] _,
    pc := Std.TreeSet.ofList [(0, 0), (1, 1)] _ }

def e1 : Equivalent (Fin 2) (Fin 2) (Fin 2) :=
  { num := Std.TreeSet.ofList [(1, 0), (1, 1)] _,
    flag := Std.TreeSet.ofList [0] _,
    unchecked := Std.TreeSet.ofList [(0, 1)] _,
    max := Std.TreeSet.ofList [(0, 1), (1, 0)] _,
    nxt := Std.TreeSet.ofList [(0, 0), (1, 1)] _,
    pc := Std.TreeSet.ofList [(1, 0), (0, 1)] _ }

#eval e0

def showPermuted (xs : List α) (σs : List (Equiv.Perm α)) : List (List α) :=
  σs.map (fun σ => xs.map σ)

def permutationDomain := permsOfList (FinEnum.toList (Fin 2))
#eval permutationDomain.length

#eval permutateEquivalent e0 (permutationDomain[1])
#eval (permutateEquivalent_ef e1 (permutationDomain[1])) == e1

#eval showPermuted [0, 1] permutationDomain

#eval compare e0 e1



def p1 := (permsOfList [1,2,3])[1]
#eval [(1,2),(2,3),(3,1)].map (fun (a,b) => (p1 a,b))

#eval showPermuted [1,2,3] (permsOfList [1,2,3])
#eval (permsOfList [1,2,3,4]).length

instance [Ord α] : Ord (List α) where
  compare :=
    let rec lex : List α → List α → Ordering
      | [], []       => .eq
      | [], _        => .lt
      | _, []        => .gt
      | a::as', b::bs' =>
        match compare a b with
        | .eq => lex as' bs'
        | o   => o
    fun a b =>
      match compare a.length b.length with
      | .eq => lex a b
      | o   => o

#eval compare [1,2,3] [2,1,3]

/-- ## TLC fingerprint algorithm
    @Override
	public final long fingerPrint(final ITool tool) {
			int sz = this.values.length;
		// TLC supports symmetry reduction. Symmetry reduction works by defining classes
		// of symmetrically equivalent states for which TLC only checks a
		// single representative of the equivalence class (orbit). E.g. in a two
		// process mutual exclusion problem, the process ids are - most of the time -
		// not relevant with regards to mutual exclusion: We don't care if process A or
		// B is in the critical section as long as only a single process is in CS. Thus
		// two states are symmetric that only differ in the process id variable value.
		// Symmetry can also be observed graphically in the state graph s.t. subgraphs
		// are isomorphic (Graph Isomorphism). Instead of enumerating the complete state
		// graph, TLC enumerates one of the isomorphic subgraphs whose state correspond
		// to the representatives. With respect to the corresponding Kripke structure M,
		// the resulting Kripke M' is called the "quotient structure" (see "Exploiting
		// Symmetry in Temporal Logic Model Checking" by Clarke et al).
		//
		// The definition of equivalence classes (orbits) is provided manually by the
		// user at startup by defining 1 to n symmetry sets. Thus TLC has to find
		// representative at runtime only which happens below. Given any state s, TLC
		// evaluates rep(s) to find the lexicographically smallest state ss = rep(s)
		// with regards to the variable values. The state ss is then fingerprint instead
		// of s.
		//
		// Evaluating rep(s) - to reduce s to ss - requires to apply all permutations in
		// the group this.perms (derived from the user-defined orbit). This is known as
		// the constructive orbit problem and is NP-hard. The loop has O(|perms| * |this.values|)
		// with |prems| = |symmetry set 1|! * |symmetry set 2|! * ... * |symmetry set n|.
        //
		// minVals is what is used to calculate/generate the fingerprint below.
		// If this state is not the lexicographically smallest state ss, its current
		// minVals will be replaced temporarily with the values of ss for the
		// calculation of the fingerprint.
		IValue[] minVals = this.values;
		if (perms != null) {
			IValue[] vals = new IValue[sz];
			// The following for loop converges to the smallest state ss under symmetry by
			// looping over all permutations applying each. If the outcome turns out to be
			// lexicographically smaller than the currently smallest, it replaces the
			// current smallest. Once all permutations (perms) have been processed, we know
			// we have found the smallest state.
			NEXT_PERM: for (int i = 0; i < perms.length; i++) {
				int cmp = 0;
				// For each value in values succinctly permute the current value
				// and compare it to its corresponding minValue in minVals.
				for (int j = 0; j < sz; j++) {
					vals[j] = this.values[j].permute(perms[i]);
					if (cmp == 0) {
						// Only compare unless an earlier compare has found a
						// difference already (if a difference has been found
						// earlier, still permute the remaining values of the
						// state to fully permute all state values).
						cmp = vals[j].compareTo(minVals[j]);
						if (cmp > 0) {
							// When cmp evaluates to >0, all subsequent
							// applications of perms[i] for the remaining values
							// won't make the resulting vals[] smaller than
							// minVals. Thus, exit preemptively from the loop
							// over vals. This works because perms is the cross
							// product of all symmetry sets.
							continue NEXT_PERM;
						}
					}
				}
				// cmp < 0 means the current state is part of a symmetry
				// permutation set/group and not the "smallest" one.
				if (cmp < 0) {
					if (minVals == this.values) {
						minVals = vals;
						vals = new IValue[sz];
					} else {
						IValue[] temp = minVals;
						minVals = vals;
						vals = temp;
					}
				}
			}
		}
		// Fingerprint the state:
		long fp = FP64.New();
		if (viewMap == null) {
			for (int i = 0; i < sz; i++) {
				fp = minVals[i].fingerPrint(fp);
			}
			if (this.values != minVals) {
				for (int i = 0; i < sz; i++) {
					this.values[i].deepNormalize();
				}
			}
		} else {
			for (int i = 0; i < sz; i++) {
				this.values[i].deepNormalize();
			}
			TLCStateMutExt state = this;
			if (minVals != this.values) {
				state = new TLCStateMutExt(minVals);
			}
			IValue val = tool.eval(viewMap, Context.Empty, state);
			fp = val.fingerPrint(fp);
		}
		return fp;
	}
-/

def s1 : Std.TreeSet (Nat × Nat) := Std.TreeSet.empty.insert (0, 1) |>.insert (2, 3)
def s2 : Std.TreeSet (Nat × Nat) := Std.TreeSet.empty.insert (1, 1) |>.insert (2, 2)
#eval s1.toArray
#eval s2.toArray
-- instance [Ord α] [Ord β] : Ord (Std.TreeSet (α × β)) where
--   compare s1 s2 :=
--     compare (s1.toArray) (s2.toArray) -- O(n)


#eval compare s1 s2
