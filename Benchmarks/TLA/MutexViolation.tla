------------------------------- MODULE MutexViolation -------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS NumProcs, NONE

Procs == 1..NumProcs

(*--algorithm mutex
{
variables locked = FALSE;
          wait_queue_num_wakers = 0;
          wait_queue_wakers = <<>>;
          has_woken = [x \in Procs |-> FALSE];

procedure lock()
{
pre_check_lock:
    if (locked = FALSE)
    {
        locked := TRUE;
        return;
    };
prepare_wait_util:
    locked := FALSE;
wait_until:
    while (TRUE)
    {
    enqueue_waker:
        wait_queue_num_wakers := wait_queue_num_wakers + 1;
        wait_queue_wakers := Append(wait_queue_wakers, self);
    check_lock:
        if (locked = FALSE)
        {
            locked := TRUE;
            has_woken[self] := TRUE;  \* drop
            return;
        };
    check_has_woken:
        await has_woken[self];
        has_woken[self] := FALSE;
    };
}

procedure unlock()
variables waker = NONE;
{
release_lock:
    locked := FALSE;
wake_one:
    if (wait_queue_num_wakers = 0)
    {
        return;
    };
wake_one_loop:
    while (TRUE)
    {
        if (wait_queue_num_wakers /= 0)
        {
            waker := Head(wait_queue_wakers);
            wait_queue_wakers := Tail(wait_queue_wakers);
            wait_queue_num_wakers := wait_queue_num_wakers - 1;
        }
        else
        {
            return;
        };
    wake_up:
        if (has_woken[waker] = FALSE)
        {
            has_woken[waker] := TRUE;
            return;
        }
    }
}

fair process (proc \in Procs)
{
start:
\*    while (TRUE)
\*    {
        call lock();
    cs:
        skip;
        call unlock();
\*    };
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2541ee33" /\ chksum(tla) = "55930485")
VARIABLES locked, wait_queue_num_wakers, wait_queue_wakers, has_woken, pc, 
          stack, waker

vars == << locked, wait_queue_num_wakers, wait_queue_wakers, has_woken, pc, 
           stack, waker >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ locked = FALSE
        /\ wait_queue_num_wakers = 0
        /\ wait_queue_wakers = <<>>
        /\ has_woken = [x \in Procs |-> FALSE]
        (* Procedure unlock *)
        /\ waker = [ self \in ProcSet |-> NONE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

pre_check_lock(self) == /\ pc[self] = "pre_check_lock"
                        /\ IF locked = FALSE
                              THEN /\ locked' = TRUE
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "prepare_wait_util"]
                                   /\ UNCHANGED << locked, stack >>
                        /\ UNCHANGED << wait_queue_num_wakers, 
                                        wait_queue_wakers, has_woken, waker >>

prepare_wait_util(self) == /\ pc[self] = "prepare_wait_util"
             /\ locked' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "wait_until"]
             /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers, 
                             has_woken, stack, waker >>

wait_until(self) == /\ pc[self] = "wait_until"
                    /\ pc' = [pc EXCEPT ![self] = "enqueue_waker"]
                    /\ UNCHANGED << locked, wait_queue_num_wakers, 
                                    wait_queue_wakers, has_woken, stack, waker >>

enqueue_waker(self) == /\ pc[self] = "enqueue_waker"
                       /\ wait_queue_num_wakers' = wait_queue_num_wakers + 1
                       /\ wait_queue_wakers' = Append(wait_queue_wakers, self)
                       /\ pc' = [pc EXCEPT ![self] = "check_lock"]
                       /\ UNCHANGED << locked, has_woken, stack, waker >>

check_lock(self) == /\ pc[self] = "check_lock"
                    /\ IF locked = FALSE
                          THEN /\ locked' = TRUE
                               /\ has_woken' = [has_woken EXCEPT ![self] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "check_has_woken"]
                               /\ UNCHANGED << locked, has_woken, stack >>
                    /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers, 
                                    waker >>

check_has_woken(self) == /\ pc[self] = "check_has_woken"
                         /\ has_woken[self]
                         /\ has_woken' = [has_woken EXCEPT ![self] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = "wait_until"]
                         /\ UNCHANGED << locked, wait_queue_num_wakers, 
                                         wait_queue_wakers, stack, waker >>

lock(self) == pre_check_lock(self) \/ prepare_wait_util(self) \/ wait_until(self)
                 \/ enqueue_waker(self) \/ check_lock(self)
                 \/ check_has_woken(self)

release_lock(self) == /\ pc[self] = "release_lock"
                      /\ locked' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "wake_one"]
                      /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers, 
                                      has_woken, stack, waker >>

wake_one(self) == /\ pc[self] = "wake_one"
                  /\ IF wait_queue_num_wakers = 0
                        THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "wake_one_loop"]
                             /\ UNCHANGED << stack, waker >>
                  /\ UNCHANGED << locked, wait_queue_num_wakers, 
                                  wait_queue_wakers, has_woken >>

wake_one_loop(self) == /\ pc[self] = "wake_one_loop"
                       /\ IF wait_queue_num_wakers /= 0
                             THEN /\ waker' = [waker EXCEPT ![self] = Head(wait_queue_wakers)]
                                  /\ wait_queue_wakers' = Tail(wait_queue_wakers)
                                  /\ wait_queue_num_wakers' = wait_queue_num_wakers - 1
                                  /\ pc' = [pc EXCEPT ![self] = "wake_up"]
                                  /\ stack' = stack
                             ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << wait_queue_num_wakers, 
                                                  wait_queue_wakers >>
                       /\ UNCHANGED << locked, has_woken >>

wake_up(self) == /\ pc[self] = "wake_up"
                 /\ IF has_woken[waker[self]] = FALSE
                       THEN /\ has_woken' = [has_woken EXCEPT ![waker[self]] = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "wake_one_loop"]
                            /\ UNCHANGED << has_woken, stack, waker >>
                 /\ UNCHANGED << locked, wait_queue_num_wakers, 
                                 wait_queue_wakers >>

unlock(self) == release_lock(self) \/ wake_one(self) \/ wake_one_loop(self)
                   \/ wake_up(self)

start(self) == /\ pc[self] = "start"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                        pc        |->  "cs" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "pre_check_lock"]
               /\ UNCHANGED << locked, wait_queue_num_wakers, 
                               wait_queue_wakers, has_woken, waker >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "Done",
                                                     waker     |->  waker[self] ] >>
                                                 \o stack[self]]
            /\ waker' = [waker EXCEPT ![self] = NONE]
            /\ pc' = [pc EXCEPT ![self] = "release_lock"]
            /\ UNCHANGED << locked, wait_queue_num_wakers, wait_queue_wakers, 
                            has_woken >>

proc(self) == start(self) \/ cs(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in Procs: proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self)) /\ WF_vars(lock(self)) /\ WF_vars(unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

MutualExclusion == \A i, j \in Procs : 
                     (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in { "pre_check_lock", "wait_until", "enqueue_waker", "check_lock", "check_has_woken"}

DeadAndLivelockFree == \E i \in Procs : 
                        Trying(i) ~> (\E j \in Procs : pc[j] = "cs")

StarvationFree == \A i \in Procs :
                        Trying(i) ~> (pc[i] = "cs")

=============================================================================
