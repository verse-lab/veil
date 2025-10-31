import Veil
-- --------------------------- MODULE Rooms -----------------------------
veil module Rooms
-- EXTENDS TLC, Naturals, FiniteSets
-- CONSTANT Room, Guest
type seq_t
instantiate seq : TotalOrderWithZero seq_t

enum Room = {Elm, Cendena}
enum Guest = {Olivier, Bruno, Aquinas}
enum Position = {noroom, room}
enum Occupied = {nobody, body}


immutable individual one : seq_t
-- VARIABLE assignedKey
-- VARIABLE registered
-- VARIABLE roomKey
-- VARIABLE guestKeys
-- VARIABLE inside
relation assignedKey : Guest → Position → Bool
relation registered : Room → Guest → Bool
relation roomKey : Room → Room → seq_t → Bool
relation guestKeys : Guest → Room → seq_t → Bool
relation inside : Room → Occupied → Bool


#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

assumption [zero_one] next seq.zero one


-- \* A helper function to issue the next key
-- NextKey(r,k) == <<r,k[2]+1>>
-- \* Hint: use "nobody" to represent an empty room and
-- \*           "noroom" to indicate that a gues is currently not in any room.

-- \* A basic coherence invariant of the system
-- TypeOK ==  /\ assignedKey \in [Guest -> {"noroom", "room"}] \* Whether a guest is inside a room
--            /\ registered \in [Room -> SUBSET Guest] \* Room-Guest dictionary
--            /\ roomKey \in [Room -> Key] \* Room-Key dictionary
--            /\ guestKeys \in [Guest -> SUBSET Key] \* Guests' keys
--            /\ inside \in [Room -> {"nobody", "body"}] \* Whether a room is occupied
/- `Veil` is type safe naturally, so we do not need check such `typeOK` property as in TLA+. -/

-- Init == /\ assignedKey = [g \in Guest |-> "noroom"]
--         /\ registered = [r \in Room |-> {}]
--         /\ roomKey = [r \in Room |-> <<r,0>>]
--         /\ guestKeys = [r \in Guest |-> {}]
--         /\ inside = [r \in Room |-> "nobody"]
-- invariant [unique_inside] inside R P1 ∧ inside R P2 → P1 = P2
-- invariant [unique_roomKey] roomKey R Q M ∧ roomKey R P N → Q = P ∧ M = N

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
-- CheckIn(g,r) == /\ Cardinality(registered[r]) = 0 \* Cannot check-in to an occupied room
--                 /\ registered' = [registered EXCEPT ![r] = registered[r] \cup {g}] \* Register the room for the guest
--                 /\ guestKeys' = [guestKeys EXCEPT ![g] = guestKeys[g] \cup {roomKey[r]}] \* Put the key into the quest's pocket
--                 /\ UNCHANGED <<assignedKey,roomKey,inside>>
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


-- EnterRoom(g,r) == /\ assignedKey[g] = "noroom" \* The person must not be in any room
--                   /\ inside[r] = "nobody" \* The room must be empty
--                   /\ Cardinality(guestKeys[g]) > 0 \* At least one key must be hold
--                   /\ roomKey[r] = RandomElement(guestKeys[g]) \* Pick a random key so that old keys might be chosen
--                   /\ assignedKey' = [assignedKey EXCEPT ![g] = "room"] \* Now the guest is in his room
--                   /\ inside' = [inside EXCEPT ![r] = "body"] \* The room's state also changed
--                   /\ UNCHANGED <<registered,roomKey,guestKeys>>
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


/- This is an extra strong condition. -/
-- require registered r g
-- LeaveRoom(g,r) == /\ assignedKey[g] = "room" \* The person must be inside his room
--                   /\ inside[r] = "body" \* The room must be occupied
--                   /\ \E k \in guestKeys[g] : k = roomKey[r] \* The person must be the one who has the correct key
--                   /\ assignedKey' = [assignedKey EXCEPT ![g] = "noroom"]
--                   /\ inside' = [inside EXCEPT ![r] = "nobody"]
--                   /\ UNCHANGED <<registered,roomKey,guestKeys>>
action LeaveRoom (g : Guest) (r : Room) {
  require assignedKey g room
  require inside r body
  require ∃a b, guestKeys g a b ∧ roomKey r a b

  assignedKey g P := P == noroom
  inside r O := O == nobody
}

-- CheckOut(g,r) == /\ g \in registered[r] \* The guest must be the registered occupant to the correct room
--                  /\ assignedKey[g] = "noroom" \* Cannot checkout if the guest is still in his/her room
--                  /\ inside[r] = "nobody" \* Cannot checkout if there is a person in the room
--                  /\ registered' = [registered EXCEPT ![r] = registered[r] \ {g}] \* Remove the registered user
--                  /\ roomKey' = [roomKey EXCEPT ![r] = NextKey(r, roomKey[r])]
--                  /\ UNCHANGED <<assignedKey,guestKeys,inside>>
-- NextKey(r,k) == <<r,k[2]+1>>
-- invariant ∀a b g r, guestKeys g a b ∧ roomKey r a b → registered r g
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

-- Next ==
--    \/ \E g \in Guest, r \in Room : CheckIn(g,r)
--    \/ \E g \in Guest, r \in Room : CheckOut(g,r)
--    \/ \E g \in Guest, r \in Room : EnterRoom(g,r)
--    \/ \E g \in Guest, r \in Room : LeaveRoom(g,r)


-- (* This is the invariant that should hold *)
-- \* 1. Room is occupied by at most one person
-- \* 2. If a guest is inside the room, he must have the correct key with the correct state (check-in, room, person states)
-- \* 3. Room state must agree with Guest state
-- NoBadEntry == /\ \A r \in Room : Cardinality(registered[r]) <= 1
--               /\ \A g \in DOMAIN assignedKey :
--                     /\ assignedKey[g] = "room" => \E r \in Room :
--                         /\ roomKey[r] \in guestKeys[g]
--                         /\ inside[r] = "body"
--                         /\ g \in registered[r]
--               /\ \A r \in DOMAIN inside :
--                     /\ inside[r] = "body" => \E g \in Guest :
--                         /\ roomKey[r] \in guestKeys[g]
--                         /\ assignedKey[g] = "room"
--                         /\ g \in registered[r]

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
-- ---------------------------------------------------------------
-- \* TODO: Work out the constraints for the state-space to make
-- \* checking of this model via TLC tractable. Use this constraints
-- \* in the Rooms.cfg file.

/- `It seems thata we can still prove the invairants even though we do not model this constraint`. -/
-- constr == \A g \in DOMAIN guestKeys : Cardinality(guestKeys[g]) <= 3
-- ===============================================================
end Rooms
