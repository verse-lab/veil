--------------------------- MODULE Room -----------------------------
EXTENDS TLC, Naturals, FiniteSets
CONSTANT Room, Guest

Key == Room \X Nat

VARIABLE assignedKey
VARIABLE registered
VARIABLE roomKey
VARIABLE guestKeys
VARIABLE inside

\* A helper function to issue the next key
NextKey(r,k) == <<r,k[2]+1>>

\* Hint: use "nobody" to represent an empty room and 
\*           "noroom" to indicate that a gues is currently not in any room.

\* A basic coherence invariant of the system
TypeOK ==  /\ assignedKey \in [Guest -> {"noroom", "room"}] \* Whether a guest is inside a room
           /\ registered \in [Room -> SUBSET Guest] \* Room-Guest dictionary
           /\ roomKey \in [Room -> Key] \* Room-Key dictionary
           /\ guestKeys \in [Guest -> SUBSET Key] \* Guests' keys
           /\ inside \in [Room -> {"nobody", "body"}] \* Whether a room is occupied
    
Init == /\ assignedKey = [g \in Guest |-> "noroom"]
        /\ registered = [r \in Room |-> {}]
        /\ roomKey = [r \in Room |-> <<r,0>>]
        /\ guestKeys = [r \in Guest |-> {}]
        /\ inside = [r \in Room |-> "nobody"]
  
CheckIn(g,r) == /\ Cardinality(registered[r]) = 0\* Cannot check-in to an occupied room
                /\ registered' = [registered EXCEPT ![r] = registered[r] \cup {g}] \* Register the room for the guest
                /\ guestKeys' = [guestKeys EXCEPT ![g] = guestKeys[g] \cup {roomKey[r]}] \* Put the key into the quest's pocket
                /\ UNCHANGED <<assignedKey,roomKey,inside>>
             
CheckOut(g,r) == /\ g \in registered[r] \* The guest must be the registered occupant to the correct room
                 /\ assignedKey[g] = "noroom" \* Cannot checkout if the guest is still in his/her room
                 /\ inside[r] = "nobody" \* Cannot checkout if there is a person in the room
                 /\ registered' = [registered EXCEPT ![r] = registered[r] \ {g}] \* Remove the registered user
                 /\ roomKey' = [roomKey EXCEPT ![r] = NextKey(r, roomKey[r])]
                 /\ UNCHANGED <<assignedKey,guestKeys,inside>>
  
EnterRoom(g,r) == /\ assignedKey[g] = "noroom" \* The person must not be in any room
                  /\ inside[r] = "nobody" \* The room must be empty
                  /\ Cardinality(guestKeys[g]) > 0 \* At least one key must be hold
                \*   /\ roomKey[r] = RandomElement(guestKeys[g]) \* Pick a random key so that old keys might be chosen
                  /\ \E k \in guestKeys[g] : k = roomKey[r] \* The person must be the one who has the correct key
                  /\ assignedKey' = [assignedKey EXCEPT ![g] = "room"] \* Now the guest is in his room
                  /\ inside' = [inside EXCEPT ![r] = "body"] \* The room's state also changed
                  /\ UNCHANGED <<registered,roomKey,guestKeys>>
       
LeaveRoom(g,r) == /\ assignedKey[g] = "room" \* The person must be inside his room
                  /\ inside[r] = "body" \* The room must be occupied
                  /\ \E k \in guestKeys[g] : k = roomKey[r] \* The person must be the one who has the correct key
                  /\ assignedKey' = [assignedKey EXCEPT ![g] = "noroom"]
                  /\ inside' = [inside EXCEPT ![r] = "nobody"]
                  /\ UNCHANGED <<registered,roomKey,guestKeys>>
   
Next == 
/\ \A g \in DOMAIN guestKeys : Cardinality(guestKeys[g]) <= 3
/\
   \/ \E g \in Guest, r \in Room : CheckIn(g,r)
   \/ \E g \in Guest, r \in Room : CheckOut(g,r)
   \/ \E g \in Guest, r \in Room : EnterRoom(g,r)
   \/ \E g \in Guest, r \in Room : LeaveRoom(g,r)

(* This is the invariant that should hold *)
\* 1. Room is occupied by at most one person
\* 2. If a guest is inside the room, he must have the correct key with the correct state (check-in, room, person states)
\* 3. Room state must agree with Guest state
NoBadEntry == /\ \A r \in Room : Cardinality(registered[r]) <= 1
              /\ \A g \in DOMAIN assignedKey : 
                    /\ assignedKey[g] = "room" => \E r \in Room : 
                        /\ roomKey[r] \in guestKeys[g]
                        /\ inside[r] = "body"
                        /\ g \in registered[r]
              /\ \A r \in DOMAIN inside :
                    /\ inside[r] = "body" => \E g \in Guest :
                        /\ roomKey[r] \in guestKeys[g]
                        /\ assignedKey[g] = "room"
                        /\ g \in registered[r]
     
---------------------------------------------------------------
\* TODO: Work out the constraints for the state-space to make 
\* checking of this model via TLC tractable. Use this constraints
\* in the Rooms.cfg file.

constr == \A g \in DOMAIN guestKeys : Cardinality(guestKeys[g]) <= 3

===============================================================
          