import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

veil module Rooms

type seq_t
-- Guarantee all the preds are decidable
instantiate seq : TotalOrderWithZero seq_t

enum Room = {Elm, Cendena}
enum Guest = {Olivier, Bruno, Aquinas}
enum Position = {noroom, room}
enum Occupied = {nobody, body}

immutable individual one : seq_t
relation assignedKey : Guest → Position → Bool
relation registered : Room → Guest → Bool
relation roomKey : Room → Room → seq_t → Bool
relation guestKeys : Guest → Room → seq_t → Bool
relation inside : Room → Occupied → Bool

#print Room_Enum

#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

assumption [zero_one] next seq.zero one


after_init {
  assignedKey G P := P == noroom
   /- `registered r g = True` means `registered = [r \in Room |-> 𝑆] ∧ g ∈ 𝑆` -/
  registered R G := false

  /- `roomKey r q n = True` means `roomKey = [r \in Room |-> <<q,n>>]` -/
  roomKey R Q N := (Q == R && N == seq.zero)
  -- roomKey R Q N := false
  -- roomKey R R seq.zero := true

   /- `guestKeys r q n = True` means `guestKeys = [r \in Room |-> 𝑆] ∧ <<q,n>> ∈ 𝑆` -/
  guestKeys R Q N := false
  inside R O := O == nobody

}


action CheckIn (g : Guest) (r : Room) {
  require ∀g, registered r g = false
  registered r g := true

  /- Read the value `<<y, n>>` from `roomKey[r]`-/
  let n ← pick seq_t
  let y ← pick Room
  assume roomKey r y n
  guestKeys g y n := true

}

procedure succ (n : seq_t) {
  let k :| next n k
  return k
}


action EnterRoom(g : Guest) (r : Room) {
  require assignedKey g noroom
  require inside r nobody
  -- Cardinality(guestKeys[g]) > 0 \* At least one key must be hold
  require ∃a b, guestKeys g a b

  /- Pick a random key so that old keys might be chosen -/
  let n ← pick seq_t
  let y ← pick Room
  assume guestKeys g y n
  if roomKey r y n then
    assignedKey g P := P == room
    inside r O := O == body
}


action LeaveRoom (g : Guest) (r : Room) {
  require assignedKey g room
  require inside r body
  require ∃a b, guestKeys g a b ∧ roomKey r a b

  assignedKey g P := P == noroom
  inside r O := O == nobody
}


action CheckOut (g : Guest) (r : Room) {
  require registered r g
  require assignedKey g noroom
  require inside r nobody
  registered r g := false
  let n ← pick seq_t
  let y ← pick Room
  assume roomKey r y n
  let ny ← succ n
  roomKey r R N := (R == r && N == ny)

}

/- `NoBadEntry` = `maunual_1` ∧ `maunual_2` ∧ `maunual_3`-/
safety [maunual_1] registered R G1 ∧ registered R G2 → G1 = G2
safety [maunual_2] ∀g, assignedKey g room → (∃r y n, (roomKey r y n ∧ guestKeys g y n) ∧ inside r body ∧ registered r g)
safety [maunual_3] ∀r, inside r body → (∃g y n, (roomKey r y n ∧ guestKeys g y n) ∧ assignedKey g room ∧ registered r g)


invariant [key_inside_is_registered]
  ∀ r g, inside r body ∧ assignedKey g room ∧ (∃ a b, guestKeys g a b ∧ roomKey r a b) → registered r g

invariant [unique_assigned_key] assignedKey G P ∧ assignedKey G Q → P = Q
invariant [unique_inside] inside R P1 ∧ inside R P2 → P1 = P2
invariant [unique_roomKey] roomKey R Q M ∧ roomKey R P N → Q = P ∧ M = N
invariant [roomKey_room_agrees] ∀ r y n, roomKey r y n → y = r
invariant [roomKey_exists] ∀ r, ∃ n, roomKey r r n


invariant [assigned_has_unique_room]
  ∀ g, assignedKey g room →
    ∃ r, registered r g ∧ inside r body ∧
         (∀ r2, registered r2 g ∧ inside r2 body → r2 = r)

invariant [no_future_keys]
  ∀ g r m k, roomKey r r m ∧ guestKeys g r k → ¬ lt m k

invariant [current_key_registration]
  ∀a b g r, guestKeys g a b ∧ roomKey r a b → registered r g



#gen_spec

#time #check_invariants

#gen_exec

#finitizeTypes (Fin 2), Room, Guest, Position, Occupied


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => no_future_keys ρ σ) ((fun ρ σ => true)) {one := 1} hash).snd
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {one := 1} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end Rooms
