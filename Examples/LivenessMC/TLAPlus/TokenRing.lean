import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/ewd426/TokenRing.tla
-- Dijkstra's self-stabilizing token ring (EWD426).

veil module TokenRing

immutable individual M : Nat

type node
immutable function pred : node → node
function c : node → Nat

-- Used purely to allow syntax close to TLA+, with parametric N/M
immutable function n : Nat → node -- Conversion function: TLA+ uses Nat directly instead of abstract types
immutable function forAllPreds : node → (node → Bool) → Bool -- \A j \in 0..i-1 notation
immutable function forAllSuccs : node → (node → Bool) → Bool -- \A j \in i..N-1 notation

#gen_state

assumption [M_pos] M > 0

-- Init == c ∈ [Node -> 0..M-1]
after_init {
  let cInit ← pick (node → Fin M)
  c N := (cInit N).val
}

-- CreateToken == c[0] = c[N-1] /\ c' = [c EXCEPT ![0] = (c[N-1]+1) % M]
action CreateToken {
  require c (n 0) = c (pred (n 0))
  c (n 0) := (c (pred (n 0)) + 1) % M
}

-- PassToken(i) == i # 0 /\ c[i] # c[i-1] /\ c' = [c EXCEPT ![i] = c[i-1]]
action PassToken (i : node) {
  require i ≠ n 0
  require c i ≠ c (pred i)
  c i := c (pred i)
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
/-action stutter {
  require false
  pure ()
}-/

-- TypeOK == c ∈ [Node -> 0..M-1]
invariant [typeOK] ∀ n, c n < M

/-
UniqueToken ==
    \E i \in 0 .. N :                           \* unique token at i (or i=N => token is at 0)
       /\ \A j \in 0..i-1: c[j]= c[0]           \* before i all c equals c[0]
       /\ \A j \in i..N-1: c[j]= (c[0]-1) % M   \* after i all c following c[0]
-/
liveness [stab]
  ◇ □ ⌜ (∃ (i:node),
          (forAllPreds i (fun j => c j = c (n 0)))
          ∧ (forAllSuccs i (fun j => c j = (c (n 0) + M - 1) % M)))
      ∨ (∀ (j:node), c j = c (n 0)) ⌝

#gen_spec


def getNodeByNat : Nat → Fin 6 := fun n => ⟨n % 6, Nat.mod_lt n (by omega)⟩
def forAllPreds' (n : Fin 6) (f : Fin 6 → Bool) : Bool :=
  Fin.foldl n.val (fun acc i => acc && f ⟨i.val, by omega⟩) true
def forAllSuccs' (n : Fin 6) (f : Fin 6 → Bool) : Bool :=
  Fin.foldl (5 - n.val) (fun acc i => acc && f ⟨n.val + 1 + i.val, by omega⟩) true

def theory0 : Theory (Fin 6) :=
  { pred := fun n => (n - 1) % 6,
    forAllPreds := forAllPreds',
    forAllSuccs := forAllSuccs',
    n := getNodeByNat,
    M := 6 }

#model_check { node := Fin 6 } theory0

#eval Veil.LivenessMC.printCheckResult "TokenRing" "<>[]UniqueToken"
  (Veil.LivenessMC.check (enumerableTransitionSystem (Fin 6) theory0)
    (stab (Theory (Fin 6)) (State (FieldConcreteType (Fin 6)))
      (Fin 6) (FieldConcreteType (Fin 6)))
    (by native_decide) (by native_decide))
