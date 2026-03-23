------------------------------ MODULE Traffic ------------------------------
\* source: https://github.com/Apress/practical-tla-plus/blob/master/Chapter%206/traffic.tla
Color == {"red", "green"}

NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
                  
(*--algorithm traffic
variables
  at_light = TRUE,
  light = "red";


fair process light = "light"
begin
  Cycle:
    while at_light do
      light := NextColor(light);
    end while;
end process;

fair+ process car = "car"
begin
  Drive:
    when light = "green";
    at_light := FALSE;
end process;
end algorithm;*)
\* BEGIN TRANSLATION
\* Process light at line 14 col 1 changed to light_
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

Next == light_ \/ car
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================