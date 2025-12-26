import Veil
veil module ben_or
-- ------------------------------- MODULE typedefs --------------------------------
-- EXTENDS Variants

-- (*
--  * Type definitions:
--  *
--  * Type-1 messages.
--  * @typeAlias: msgOne = { src: REPLICA, r: Int, v: Int };
--  *
--  * Type-2 messages.
--  * @typeAlias: msgTwo = Q({ src: REPLICA, r: Int }) | D({ src: REPLICA, r: Int, v: Int });
--  *)
-- typedefs_aliases == TRUE

-- \* predefined constants for the steps
-- S1 == "S1_OF_STEP"
-- S2 == "S2_OF_STEP"
-- S3 == "S3_OF_STEP"
-- @[veil_decl]
-- inductive Step where
--   | S1_OF_STEP
--   | S2_OF_STEP
--   | S3_OF_STEP
-- deriving instance Veil.Enumeration for Step
enum Step = { S1_OF_STEP, S2_OF_STEP, S3_OF_STEP }

-- \* @type: (REPLICA, Int, Int) => $msgOne;
-- M1(src, round, value) == [ src |-> src, r |-> round, v |-> value ]
@[veil_decl]
structure M1 (src rty vty : Type) where
  src : src
  r : rty
  v : vty
deriving instance Veil.Enumeration for M1


-- \* @type: (REPLICA, Int) => $msgTwo;
-- Q2(src, round) == Variant("Q", [ src |-> src, r |-> round ])
@[veil_decl]
inductive Tag where
  | Q2
  | D2
deriving instance Veil.Enumeration for Tag


@[veil_decl]
structure M2 (src rty vty : Type) where
  tag : Tag
  src : src
  r : rty
  v : vty
deriving instance Veil.Enumeration for M2
-- \* @type: $msgTwo => Bool;
-- IsQ2(msg) == VariantTag(msg) = "Q"

-- \* @type: $msgTwo => { src: REPLICA, r: Int };
-- AsQ2(msg) == VariantGetUnsafe("Q", msg)

-- \* @type: (REPLICA, Int, Int) => $msgTwo;
-- D2(src, round, value) == Variant("D", [ src |-> src, r |-> round, v |-> value ])

-- \* @type: $msgTwo => Bool;
-- IsD2(msg) == VariantTag(msg) = "D"

-- \* @type: $msgTwo => { src: REPLICA, r: Int, v: Int };
-- AsD2(msg) == VariantGetUnsafe("D", msg)

-- ================================================================================

-- --------------------------------- MODULE Ben_or83 ------------------------------------
-- (*
--  * This is a TLA+ specification of the Ben-Or's solution to the Byzantine consensus
--  * problem. The algorithm is described in the paper:
--  *
--  * M. Ben-Or. Another advantage of free choice (extended abstract). PODC 1983.
--  *
--  * The algorithm is probabilistic. We focus on safety and, therefore, abstract
--  * probabilities with non-determinism.
--  *
--  * Igor Konnov, 2024
--  *)
-- EXTENDS FiniteSets, Integers, typedefs

-- \* The set of values to choose from
-- VALUES == { 0, 1 }

-- CONSTANTS
--     \* The total number of replicas.
--     \* @type: Int;
--     N,
--     \* An upper bound on the number of faulty replicas.
--     \* @type: Int;
--     T,
--     \* The actual number of faulty replicas (unknown to the replicas).
--     \* @type: Int;
--     F,
type replica
type ReplicaSet
instantiate rset : TSet replica ReplicaSet
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
--     \* The set of the correct (honest) replicas.
--     \* @type: Set(REPLICA);
--     CORRECT,
immutable individual Correct : ReplicaSet
--     \* The set of the Byzantine (faulty) replicas.
--     \* @type: Set(REPLICA);
immutable individual Faulty : ReplicaSet
--     FAULTY,
--     \* The set of rounds, which we bound for model checking.
--     \* @type: Set(Int);
--     ROUNDS

-- ALL == CORRECT \union FAULTY
-- NO_DECISION == -1

-- ASSUME N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F
-- ASSUME 1 \in ROUNDS
-- ASSUME NO_DECISION \notin VALUES

-- VARIABLES
--   \* The current value by a replica, called $x_P$ in the paper.
--   \* @type: REPLICA -> Int;
--   value,
type round
type RoundSet
instantiate roundSet : TSet round RoundSet
immutable individual ROUNDS : RoundSet
instantiate seq : TotalOrderWithZero round
type value
type ValueSet
instantiate valSet : TSet value ValueSet
immutable individual VALUES : ValueSet
immutable individual NO_DECISION : value
function fValue : replica → value
--   \* The decision by a replica, where -1 means no decision.
--   \* @type: REPLICA -> Int;
--   decision,
function fDecision : replica → value
--   \* The round number of a replica, called $r$ in the paper.
--   \* @type: REPLICA -> Int;
--   round,
function fRound : replica → round
--   \* The replica step: S1, S2, S3.
--   \* @type: REPLICA -> STEP;
--   step,
function fStep : replica → Step
--   \* Type-1 messages sent by the correct and faulty replicas, mapped by rounds.
--   \* @type: Int -> Set($msgOne);
--   msgs1,
type msgOne
instantiate msgOneSet : TSet (M1 replica round value) msgOne
--   \* Type-2 messages sent by the correct and faulty replicas, mapped by rounds.
--   \* @type: Int -> Set($msgTwo);
--   msgs2
type msgTwo
instantiate msgTwoSet : TSet (M2 replica round value) msgTwo
-- \* @type: Set($msgOne) => Set(REPLICA);
-- Senders1(m1s) ==
--   \* Filter the set of ALL, as it has fixed size, in contrast to m1s.
--   \* This is especially important, when we call Cardinality on the result.
--   { id \in ALL: \E m \in m1s: m.src = id }
function msg1 : round → msgOne
function msg2 : round → msgTwo

#gen_state

theory ghost relation lt (x y : round) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : round) := (lt x y ∧ ∀ z, lt x z → seq.le y z)
assumption [nat_gt_zero] ∀n, seq.le seq.zero n



procedure succ (n : round) {
  let k :| next n k
  return k
}

procedure Senders1(m1s : msgOne) {
  let ids : ReplicaSet := msgOneSet.map m1s (fun m => m.src)
  return ids
}

-- \* @type: Set($msgTwo) => Set(REPLICA);
-- Senders2(m2s) ==
--   \* Filter the set of ALL, as it has fixed size, in contrast to m2s.
--   \* This is especially important, when we call Cardinality on the result.
--   { id \in ALL:
--     \E m \in m2s: (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id) }
procedure Senders2(m2s : msgTwo) {
  -- let idsD : ReplicaSet := msgTwoSet.filter m2s (fun m => m.tag == Tag.D2)
  let D2Set : msgTwo := msgTwoSet.filter m2s (fun m => m.tag == Tag.D2)
  let idsD : ReplicaSet := msgTwoSet.map D2Set (fun m => m.src)
  let Q2Set : msgTwo := msgTwoSet.filter m2s (fun m => m.tag == Tag.Q2)
  let idsQ : ReplicaSet := msgTwoSet.map Q2Set (fun m => m.src)
  return rset.union idsD idsQ
}

ghost relation isCorrect (r : replica) := rset.contains r Correct
ghost relation isFaulty (r : replica) := rset.contains r Faulty
-- Init ==
--   \* non-deterministically choose the initial values
--   /\ value \in [ CORRECT -> VALUES ]
--   /\ decision = [ r \in CORRECT |-> NO_DECISION ]
--   /\ round = [ r \in CORRECT |-> 1 ]
--   /\ step = [ r \in CORRECT |-> S1 ]
--   /\ msgs1 = [ r \in ROUNDS |-> {}]
--   /\ msgs2 = [ r \in ROUNDS |-> {}]
after_init {
  fValue P := *
  fDecision P := NO_DECISION
  fRound R := * -- one
  fStep P := S1_OF_STEP
  msg1 R := msgOneSet.empty
  msg2 R := msgTwoSet.empty
  -- msgs1 and msgs2 are initialized as empty sets for all rounds
}

-- InitWithFaults ==
--   \* non-deterministically choose the initial values
--   /\ value \in [ CORRECT -> VALUES ]
--   /\ decision = [ r \in CORRECT |-> NO_DECISION ]
--   /\ round = [ r \in CORRECT |-> 1 ]
--   /\ step = [ r \in CORRECT |-> S1 ]
--   \* non-deterministically initialize the messages with faults
--   /\ \E F1 \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ]:
--         msgs1 = [ r \in ROUNDS |-> { m \in F1: m.r = r } ]
--   /\ \E F1D \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ],
--         F1Q \in SUBSET [ src: FAULTY, r: ROUNDS ]:
--         msgs2 = [ r \in ROUNDS |->
--             { D2(mm.src, r, mm.v): mm \in { m \in F1D: m.r = r } }
--                 \union { Q2(mm.src, r): mm \in { m \in F1Q: m.r = r } }
--         ]


-- \* @type: REPLICA => Bool;
-- Step1(id) ==
--   Step1::
--   LET r == round[id] IN
--   /\ step[id] = S1
--   \* "send the message (1, r, x_P) to all the processes"
--   /\ msgs1' = [msgs1 EXCEPT ![r] = @ \union { M1(id, r, value[id]) }]
--   /\ step' = [step EXCEPT ![id] = S2]
--   /\ UNCHANGED << value, decision, round, msgs2 >>
action Step1 (rep : replica) {
  require isCorrect rep
  require fStep rep == S1_OF_STEP
  let rd : round := fRound rep
  let val : value := fValue rep
  msg1 rd := msgOneSet.insert
    { src := rep,
      r := rd,
      v := val} (msg1 rd)
  fStep rep := S2_OF_STEP
}


-- Step2(id) ==
--   Step2::
--   LET r == round[id] IN
--   /\ step[id] = S2
--   /\ \E received \in SUBSET msgs1[r]:
--      \* "wait till messages of type (1, r, *) are received from N - T processes"
--      /\ Cardinality(Senders1(received)) >= N - T
--      /\ LET Weights == [ v \in VALUES |->
--           Cardinality(Senders1({ m \in received: m.v = v })) ]
--         IN
--         \/ \E v \in VALUES:
--           \* "if more than (N + T)/2 messages have the same value v..."
--           /\ 2 * Weights[v] > N + T
--           \* "...then send the message (2, r, v, D) to all processes"
--           /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { D2(id, r, v) }]
--         \//\ \A v \in VALUES: 2 * Weights[v] <= N + T
--           \* "Else send the message (2, r, ?) to all processes"
--           /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { Q2(id, r) }]
--   /\ step' = [ step EXCEPT ![id] = S3 ]
--   /\ UNCHANGED << value, decision, round, msgs1 >>

-- procedure Senders1(m1s : msgOne) {
--   let ids : ReplicaSet := msgOneSet.map m1s (fun m => m.src)
--   return ids
-- }

procedure Weights1 (received : msgOne) (v : value) {
  -- Filter messages with value v: { m \in received: m.v = v }
  let messagesWithV := msgOneSet.filter received (fun m => m.v = v)
  -- Get senders of those messages: Senders1(...)
  let senders ← Senders1 messagesWithV
  -- Return the cardinality: Cardinality(...)
  return rset.count senders
}

ghost relation weights1_leq (received : msgOne) (v : value) (Tn : Nat) :=
  let messagesWithV := msgOneSet.filter received (fun m => m.v = v)
  let senders : ReplicaSet := msgOneSet.map messagesWithV (fun m => m.src)
  rset.count senders <= Tn


ghost relation less_than_N_plus_T_div_2 (received : msgOne) :=
  -- 2 * weightV <= N + T
  (valSet.toList VALUES) |>.all (fun v =>
    let messagesWithV := msgOneSet.filter received (fun m => m.v == v)
    let senders : ReplicaSet := msgOneSet.map messagesWithV (fun m => m.src)
    2 * (rset.count senders) <= N + T
  )

action Step2 (rep : replica) {
  require isCorrect rep
  require fStep rep == S2_OF_STEP
  let rd : round := fRound rep
  let received :| ∀m, msgOneSet.contains m received → msgOneSet.contains m (msg1 rd)
  let senders ← Senders1 received
  require rset.count senders >= N - T
  let v ← pick value
  let weightV ← Weights1 received v
  if decide $ 2 * weightV > N + T then
    -- send D2 message
    msg2 rd := msgTwoSet.insert
      { tag := Tag.D2,
        src := rep,
        r := rd,
        v := v } (msg2 rd)
  else -- send Q2 message
    -- require ∀v2, weights1_leq received v2 ( (N + T) / 2 )
    -- require (valSet.toList VALUES).all (fun v2 => weights1_leq received v2 ( (N + T) / 2 ))
    -- require less_than_N_plus_T_div_2 received
    msg2 rd := msgTwoSet.insert
      { tag := Tag.Q2,
        src := rep,
        r := rd,
        v := default } (msg2 rd)
  fStep rep := S3_OF_STEP
}


-- Step3(id) ==
--   Step3::
--   LET r == round[id] IN
--   /\ step[id] = S3
--   /\ \E received \in SUBSET msgs2[r]:
--     \* "Wait till messages of type (2, r, *) arrive from N - T processes"
--     /\ Cardinality(Senders2(received)) = N - T
--     /\ LET Weights == [ v \in VALUES |->
--              Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) ]
--        IN
--        \/ \E v \in VALUES:
--           \* "(a) If there are at least T+1 D-messages (2, r, v, D),
--           \* then set x_P to v"
--           /\ Weights[v] >= T + 1
--           /\ value' = [value EXCEPT ![id] = v]
--           \* "(b) If there are more than (N + T)/2 D-messages..."
--           /\ IF 2 * Weights[v] > N + T
--              \* "...then decide v"
--              THEN decision' = [decision EXCEPT ![id] = v]
--              ELSE decision' = decision
--        \/ /\ \A v \in VALUES: Weights[v] < T + 1
--           /\ \E next_v \in VALUES:
--              \* "(c) Else set x_P = 1 or 0 each with probability 1/2."
--              \* We replace probabilites with non-determinism.
--              /\ value' = [value EXCEPT ![id] = next_v]
--              /\ decision' = decision
--     \* the condition below is to bound the number of rounds for model checking
--     /\ r + 1 \in ROUNDS
--     \* "Set r := r + 1 and go to step 1"
--     /\ round' = [ round EXCEPT ![id] = r + 1 ]
--     /\ step' = [ step EXCEPT ![id] = S1 ]
--     /\ UNCHANGED << msgs1, msgs2 >>
procedure Weights2 (received : msgTwo) (v : value) {
  -- Filter messages with value v: { m \in received: IsD2(m) /\ AsD2(m).v = v }
  let messagesWithV := msgTwoSet.filter received (fun m => m.tag == Tag.D2 && m.v == v)
  -- Get senders of those messages: Senders2(...)
  let senders ← Senders2 messagesWithV
  -- Return the cardinality: Cardinality(...)
  return rset.count senders
}

ghost relation weights2_leq (received : msgTwo) (v : value) (Tn : Nat) :=
  let messagesWithV := msgTwoSet.filter received (fun m => m.tag == Tag.D2 && m.v == v)
  let senders : ReplicaSet := msgTwoSet.map messagesWithV (fun m => m.src)
  rset.count senders <= Tn


-- action Step3 (rep : replica) {
--   require isCorrect rep
--   require fStep rep == S3_OF_STEP
--   let rd : round := fRound rep
--   let received : msgTwo :| ∀m, msgTwoSet.contains m received → msgTwoSet.contains m (msg2 rep)
--   let senders ← Senders2 received
--   require rset.count senders == N - T
--   let v ← pick value
--   let weightV ← Weights2 received v
--   if weightV >= T + 1 then
--     -- (a) set x_P to v
--     fValue rep := v
--     if 2 * weightV > N + T then
--       -- decide v
--       fDecision rep := v
--     else
--       fDecision rep := fDecision rep
--   else
--     require ∀v2, weights2_leq received v2 (T + 1)
--     let next_v ← pick value
--     -- (c) set x_P = next_v
--     fValue rep := next_v
--     fDecision rep := fDecision rep
--   let succ_rd ← succ rd
--   require roundSet.contains succ_rd ROUNDS
--   -- set r := r + 1 and go to step 1
--   fRound rep := succ_rd
--   fStep rep := S1_OF_STEP
-- }


-- FaultyStep ==
--     \* the faulty replicas collectively inject messages for a single round
--     Faulty::
--     /\ \E r \in ROUNDS:
--         /\ \E F1 \in SUBSET [ src: FAULTY, r: { r }, v: VALUES ]:
--             msgs1' = [ msgs1 EXCEPT ![r] = @ \union F1 ]
--         /\ \E F2D \in SUBSET { D2(src, r, v): src \in FAULTY, v \in VALUES }:
--              \E F2Q \in SUBSET { Q2(src, r): src \in FAULTY }:
--                 msgs2' = [ msgs2 EXCEPT ![r] = @ \union F2D \union F2Q ]
--     /\ UNCHANGED << value, decision, round, step >>
-- action FaultyStep {
--   let r :| roundSet.contains r ROUNDS
--   let F1 : msgOne :| ∀m, msgOneSet.contains m F1 → (isFaulty m.src ∧ m.r == r)
--   msg1 r := msgOneSet.union F1 (msg1 r)
  -- let F2D : msgTwo :| ∀m, msgTwoSet.contains m F2D → (isFaulty m.src ∧ m.r == r ∧ m.tag == Tag.D2)
  -- let F2Q : msgTwo :| ∀m, msgTwoSet.contains m F2Q → (isFaulty m.src ∧ m.r == r ∧ m.tag == Tag.Q2)
  -- msg2 r := msgTwoSet.union F2D (msgTwoSet.union F2Q (msg2 r))
-- }


-- CorrectStep ==
--   \E id \in CORRECT:
--     \/ Step1(id)
--     \/ Step2(id)
--     \/ Step3(id)

-- Next ==
--   \/ CorrectStep
--   \/ FaultyStep

-- \****************** INVARIANTS *****************************

-- \* No two correct replicas decide on different values
-- AgreementInv ==
--     \A id1, id2 \in CORRECT:
--         \/ decision[id1] = NO_DECISION
--         \/ decision[id2] = NO_DECISION
--         \/ decision[id1] = decision[id2]
invariant [agreement_inv]
  ∀ id1 id2 : replica,
    isCorrect id1 ∧ isCorrect id2 →
      (fDecision id1 == NO_DECISION ∨
       fDecision id2 == NO_DECISION ∨
       fDecision id1 == fDecision id2)

invariant [msgOnesize_trivial]
  ∀ r : round,
    msgOneSet.count (msg1 r) < 1
-- \* Once a correct replica decides, it never changes its decision
-- FinalityInv ==
--     \A id \in CORRECT:
--         \/ decision[id] = NO_DECISION
--         \/ \/ decision'[id] /= NO_DECISION
--            \/ decision'[id] = decision[id]
-- invariant [finality_inv]
--   ∀ id : replica,
--     isCorrect id →
--       (fDecision id == NO_DECISION ∨
--        (fDecision id' ≠ NO_DECISION ∨
--         fDecision id' == fDecision id))
#gen_spec

set_option synthInstance.maxHeartbeats 100000
-- set_option synthInstance.maxSize 2000
#model_check
{ replica := Fin 3
  ReplicaSet := Std.ExtTreeSet (Fin 3) compare
  round := Fin 2
  RoundSet := Std.ExtTreeSet (Fin 2) compare
  value := Fin 2
  msgOne := Std.ExtTreeSet (M1 (Fin 3) (Fin 2) (Fin 2)) compare
  msgTwo := Std.ExtTreeSet (M2 (Fin 3) (Fin 2) (Fin 2)) compare
  ValueSet := Std.ExtTreeSet (Fin 2) compare
}
{
  N := 3
  T := 2
  F := 1
  Correct := (∅ : Std.ExtTreeSet (Fin 3) compare).insertMany [0, 1]
  Faulty := (∅ : Std.ExtTreeSet (Fin 3) compare).insertMany [2]
  ROUNDS := (∅ : Std.ExtTreeSet (Fin 2) compare).insertMany [0, 1]
  NO_DECISION := 0
  VALUES := (∅ : Std.ExtTreeSet (Fin 2) compare).insertMany [0, 1]
  }
-- \****************** EXAMPLES   *****************************

-- \* An example of a replica that has made a decision
-- DecisionEx ==
--     ~(\E id \in CORRECT: decision[id] /= NO_DECISION)

-- \* An example of all correct replicas having made a decision
-- AllDecisionEx ==
--     ~(\A id \in CORRECT: decision[id] /= NO_DECISION)

-- \* simple view
-- View == <<
--     { value[id]: id \in CORRECT },
--     { decision[id]: id \in CORRECT },
--     { round[id]: id \in CORRECT },
--     { step[id]: id \in CORRECT }
-- >>

-- \* Count the number of replicas that map to a value.
-- \* @type: (REPLICA -> a) => (a -> Int);
-- CountImg(f) ==
--     LET V == {f[id]: id \in CORRECT} IN
--     [ v \in V |-> Cardinality({ id \in CORRECT: f[id] = v })]

-- PreciseView == <<
--     CountImg(value),
--     CountImg(decision),
--     CountImg(round),
--     CountImg(step)
-- >>
-- ======================================================================================

end ben_or
