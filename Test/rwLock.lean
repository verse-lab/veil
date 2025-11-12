-- ----------------------------- MODULE rwlock_conform -----------------------------
import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

veil module rwlock
-- \* Abstracted:  MAX_READER

-- EXTENDS Integers, FiniteSets, Sequences, TLC

-- CONSTANTS \*NumProcs
-- Procs
-- CONSTANTS NONE, READER, WRITER, UPREADER  \* role

-- \*Procs == 1..NumProcs

-- (*--algorithm RWLock
-- {
-- variables writer_lock = FALSE;
--           upgradeable_reader_lock = FALSE;
--           upgraded = FALSE;
--           reader_lock_count = 0;
--           role = [i \in Procs |-> NONE];

-- macro _drop_write()
-- {
--     writer_lock := FALSE;
-- }

-- macro _drop_upgradeable()
-- {
--     assert(upgradeable_reader_lock = TRUE);
--     upgradeable_reader_lock := FALSE;
-- }

-- procedure change_role()
-- {
-- may_change_role:
--     either
--     {
--         return;
--     }
--     or
--     {
--         if (role[self] = READER)
--         {
--             return;
--         }
--         else if (role[self] = WRITER)
--         {
--             call downgrade();
--             return;
--         }
--         else if (role[self] = UPREADER)
--         {
--             call upgrade();
--             return;
--         }
--         else
--         {
--             assert(FALSE);
--             return;
--         }
--     };
-- }

-- procedure read()
-- {
-- try_read:
--     \* we don't save previous value of reader_lock_count because it is not checked
--     reader_lock_count := reader_lock_count + 1;
--     if (~writer_lock /\ ~upgraded)  \* assume reader count won't overflow
--     {
--         role[self] := READER;
--         return;
--     }
--     else
--     {
--     try_read_failed:
--         reader_lock_count := reader_lock_count - 1;
--         goto try_read;
--     };
-- }

-- procedure drop_read()
-- {
-- unlock_read:
--     assert(reader_lock_count > 0);
--     reader_lock_count := reader_lock_count - 1;
--     role[self] := NONE;
--     return;
-- }

-- procedure write()
-- {
-- try_write:+
--     if (~writer_lock /\ ~upgradeable_reader_lock /\ ~upgraded /\ reader_lock_count = 0)  \* lock == 0
--     {
--         writer_lock := TRUE;
--         role[self] := WRITER;
--         return;
--     }
--     else
--     {
--         goto try_write;
--     };
-- }

-- procedure drop_write()
-- {
-- unlock_write:
--     _drop_write();
--     role[self] := NONE;
--     return;
-- }

-- procedure upread()
-- variable pre_val;
-- {
-- \* disable_preempt?
-- try_upread:
--     pre_val := <<upgradeable_reader_lock, writer_lock>>;
--     upgradeable_reader_lock := TRUE;
-- try_upread_check:+
--     if (~pre_val[1] /\ ~pre_val[2])  \* lock & (WRITER | UPGRADEABLE_READER) == 0
--     {
--     try_upread_check_success:+
--         role[self] := UPREADER;
--         return;
--     }
--     else if (~pre_val[1] /\ pre_val[2])  \* WRITER
--     {
--         assert(upgradeable_reader_lock = TRUE);
--         upgradeable_reader_lock := FALSE;
--         goto try_upread;
--     }
--     else
--     {
--         goto try_upread;
--     };
-- };

-- procedure drop_upgradeable()
-- {
-- unlock_upgradeable:
--     _drop_upgradeable();
--     role[self] := NONE;
--     return;
-- }

-- procedure upgrade()
-- {
-- being_upgraded:
--     upgraded := TRUE;
-- try_upgrade:+
--     if (upgradeable_reader_lock /\ upgraded /\ ~writer_lock /\ reader_lock_count = 0)
--     {
--         writer_lock := TRUE;
--         upgradeable_reader_lock := TRUE;
--         upgraded := FALSE;
--         reader_lock_count := 0;
--     upgrade_drop_guard:
--         _drop_upgradeable();
--         role[self] := WRITER;
--         return;
--     }
--     else
--     {
--         goto try_upgrade;
--     };
-- }

-- procedure downgrade()
-- {
-- try_downgrade:+
--     if (writer_lock /\ ~upgradeable_reader_lock /\ ~upgraded /\ reader_lock_count = 0)
--     {
--         upgradeable_reader_lock := TRUE;
--         writer_lock := FALSE;
--         upgraded := FALSE;
--         reader_lock_count := 0;
--     downgrade_drop_guard:
--         _drop_write();
--         role[self] := UPREADER;
--         return;
--     }
--     else
--     {
-- \*        assert(FALSE);  \* always success
--         goto try_downgrade;
--     };
-- }

-- fair process (proc \in Procs)
-- {
-- start:
--     while (TRUE)
--     {
--         either
--         {
--             call read();
--         }
--         or
--         {
--             call upread();
--         }
--         or
--         {
--             call write();
--         };
--     may_change_role1:
--         call change_role();
--     cs1:
--         skip;
--     drop:
--         if (role[self] = READER)
--         {
--             call drop_read();
--         }
--         else if (role[self] = WRITER)
--         {
--             call drop_write();
--         };
--         else if (role[self] = UPREADER)
--         {
--             call drop_upgradeable();
--         }
--         else
--         {
--             assert(FALSE);
--         };
--     };
-- }

-- }
-- *)
-- \* BEGIN TRANSLATION (chksum(pcal) = "b1eec14a" /\ chksum(tla) = "1a4d9b6a")
-- CONSTANT defaultInitValue
-- VARIABLES writer_lock, upgradeable_reader_lock, upgraded, reader_lock_count,
--           role, pc, stack, pre_val

-- vars == << writer_lock, upgradeable_reader_lock, upgraded, reader_lock_count,
--            role, pc, stack, pre_val >>
-- CONSTANTS NONE, READER, WRITER, UPREADER  \* role
type process
enum roles = {NONE, READER, WRITER, UPREADER}
enum states = {
  start,
  may_change_role,
  try_downgrade,
  try_read,
  try_read_failed,
  unlock_readl,
  try_write,
  unlock_write,
  try_upread,
  try_upread_check,
  try_upread_check_success,
  unlock_upgradeable,
  being_upgraded,
  try_upgrade,
  downgrade_drop_guard
}
individual writer_lock : Bool
individual upgradeable_reader_lock : Bool
individual upgraded : Bool
individual reader_lock_count : Nat
relation role : process → roles → Bool
relation pc : process → states → Bool
function stack_pc : process → List states
function stack_preVal : process → List (states × states)
function pre_val : process → (states × states)
--                                                               pc        |->  "may_change_role1",
--                                                               pre_val   |->  pre_val[self] ] >>
-- ProcSet == (Procs)

-- Init == (* Global variables *)
--         /\ writer_lock = FALSE
--         /\ upgradeable_reader_lock = FALSE
--         /\ upgraded = FALSE
--         /\ reader_lock_count = 0
--         /\ role = [i \in Procs |-> NONE]
--         (* Procedure upread *)
--         /\ pre_val = [ self \in ProcSet |-> defaultInitValue]
--         /\ stack = [self \in ProcSet |-> << >>]
--         /\ pc = [self \in ProcSet |-> "start"]
#gen_state
after_init {
  writer_lock := false
  upgradeable_reader_lock := false
  upgraded := false
  reader_lock_count := 0
  role P R := R == NONE
  pc P S := S == start
  stack_pc P := []
  stack_preVal P := []
  pre_val P := (start, start)
}


-- may_change_role(self) == /\ pc[self] = "may_change_role"
--                          /\ \/ /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                             \/ /\ IF role[self] = READER
--                                      THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                                      ELSE /\ IF role[self] = WRITER
--                                                 THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "downgrade",
--                                                                                               pc        |->  Head(stack[self]).pc ] >>
--                                                                                           \o Tail(stack[self])]
--                                                      /\ pc' = [pc EXCEPT ![self] = "try_downgrade"]
--                                                 ELSE /\ IF role[self] = UPREADER
--                                                            THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "upgrade",
--                                                                                                          pc        |->  Head(stack[self]).pc ] >>
--                                                                                                      \o Tail(stack[self])]
--                                                                 /\ pc' = [pc EXCEPT ![self] = "being_upgraded"]
--                                                            ELSE /\ Assert((FALSE),
--                                                                           "Failure of assertion at line 57, column 13.")
--                                                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                          /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                          upgraded, reader_lock_count, role,
--                                          pre_val >>
-- Introduce something like `cases on`
action _may_change_role_not_change (self : process) {
  require pc self may_change_role
  pc self S := S == (stack_pc self).head!
  stack_pc self := (stack_pc self).tail
}

action _may_change_role_yes_change (self : process) {
  require pc self may_change_role
  require role self READER
  if role self READER then
    pc self S := S == (stack_pc self).head!
    stack_pc self := (stack_pc self).tail
    stack_preVal self := stack_preVal self
  else
    if role self WRITER then
      pc self S := S == try_downgrade
      stack_preVal self := stack_preVal self
    else
      if role self UPREADER then
        -- stack_pc self := [{procedure := being_upgraded, pc := (stack_pc self).head!} :: (stack_pc self).tail]
        pc self S := S == being_upgraded
        stack_preVal self := stack_preVal self
      else
        pc self S := S == (stack_pc self).head!
        stack_pc self := (stack_pc self).tail
        stack_preVal self := stack_preVal self
}



-- change_role(self) == may_change_role(self)

-- try_read(self) == /\ pc[self] = "try_read"
--                   /\ reader_lock_count' = reader_lock_count + 1
--                   /\ IF ~writer_lock /\ ~upgraded
--                         THEN /\ role' = [role EXCEPT ![self] = READER]
--                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                         ELSE /\ pc' = [pc EXCEPT ![self] = "try_read_failed"]
--                              /\ UNCHANGED << role, stack >>
--                   /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                   upgraded, pre_val >>

-- try_read_failed(self) == /\ pc[self] = "try_read_failed"
--                          /\ reader_lock_count' = reader_lock_count - 1
--                          /\ pc' = [pc EXCEPT ![self] = "try_read"]
--                          /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                          upgraded, role, stack, pre_val >>

-- read(self) == try_read(self) \/ try_read_failed(self)

-- unlock_read(self) == /\ pc[self] = "unlock_read"
--                      /\ Assert((reader_lock_count > 0),
--                                "Failure of assertion at line 84, column 5.")
--                      /\ reader_lock_count' = reader_lock_count - 1
--                      /\ role' = [role EXCEPT ![self] = NONE]
--                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                      /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                      upgraded, pre_val >>

-- drop_read(self) == unlock_read(self)

-- try_write(self) == /\ pc[self] = "try_write"
--                    /\ IF ~writer_lock /\ ~upgradeable_reader_lock /\ ~upgraded /\ reader_lock_count = 0
--                          THEN /\ writer_lock' = TRUE
--                               /\ role' = [role EXCEPT ![self] = WRITER]
--                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                          ELSE /\ pc' = [pc EXCEPT ![self] = "try_write"]
--                               /\ UNCHANGED << writer_lock, role, stack >>
--                    /\ UNCHANGED << upgradeable_reader_lock, upgraded,
--                                    reader_lock_count, pre_val >>

-- write(self) == try_write(self)

-- unlock_write(self) == /\ pc[self] = "unlock_write"
--                       /\ writer_lock' = FALSE
--                       /\ role' = [role EXCEPT ![self] = NONE]
--                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                       /\ UNCHANGED << upgradeable_reader_lock, upgraded,
--                                       reader_lock_count, pre_val >>

-- drop_write(self) == unlock_write(self)

-- try_upread(self) == /\ pc[self] = "try_upread"
--                     /\ pre_val' = [pre_val EXCEPT ![self] = <<upgradeable_reader_lock, writer_lock>>]
--                     /\ upgradeable_reader_lock' = TRUE
--                     /\ pc' = [pc EXCEPT ![self] = "try_upread_check"]
--                     /\ UNCHANGED << writer_lock, upgraded, reader_lock_count,
--                                     role, stack >>

-- try_upread_check(self) == /\ pc[self] = "try_upread_check"
--                           /\ IF ~pre_val[self][1] /\ ~pre_val[self][2]
--                                 THEN /\ pc' = [pc EXCEPT ![self] = "try_upread_check_success"]
--                                      /\ UNCHANGED upgradeable_reader_lock
--                                 ELSE /\ IF ~pre_val[self][1] /\ pre_val[self][2]
--                                            THEN /\ Assert((upgradeable_reader_lock = TRUE),
--                                                           "Failure of assertion at line 129, column 9.")
--                                                 /\ upgradeable_reader_lock' = FALSE
--                                                 /\ pc' = [pc EXCEPT ![self] = "try_upread"]
--                                            ELSE /\ pc' = [pc EXCEPT ![self] = "try_upread"]
--                                                 /\ UNCHANGED upgradeable_reader_lock
--                           /\ UNCHANGED << writer_lock, upgraded,
--                                           reader_lock_count, role, stack,
--                                           pre_val >>

-- try_upread_check_success(self) == /\ pc[self] = "try_upread_check_success"
--                                   /\ role' = [role EXCEPT ![self] = UPREADER]
--                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                   /\ pre_val' = [pre_val EXCEPT ![self] = Head(stack[self]).pre_val]
--                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                                   /\ UNCHANGED << writer_lock,
--                                                   upgradeable_reader_lock,
--                                                   upgraded, reader_lock_count >>

-- upread(self) == try_upread(self) \/ try_upread_check(self)
--                    \/ try_upread_check_success(self)

-- unlock_upgradeable(self) == /\ pc[self] = "unlock_upgradeable"
--                             /\ Assert((upgradeable_reader_lock = TRUE),
--                                       "Failure of assertion at line 28, column 5 of macro called at line 142, column 5.")
--                             /\ upgradeable_reader_lock' = FALSE
--                             /\ role' = [role EXCEPT ![self] = NONE]
--                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                             /\ UNCHANGED << writer_lock, upgraded,
--                                             reader_lock_count, pre_val >>

-- drop_upgradeable(self) == unlock_upgradeable(self)

-- being_upgraded(self) == /\ pc[self] = "being_upgraded"
--                         /\ upgraded' = TRUE
--                         /\ pc' = [pc EXCEPT ![self] = "try_upgrade"]
--                         /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                         reader_lock_count, role, stack,
--                                         pre_val >>

-- try_upgrade(self) == /\ pc[self] = "try_upgrade"
--                      /\ IF upgradeable_reader_lock /\ upgraded /\ ~writer_lock /\ reader_lock_count = 0
--                            THEN /\ writer_lock' = TRUE
--                                 /\ upgradeable_reader_lock' = TRUE
--                                 /\ upgraded' = FALSE
--                                 /\ reader_lock_count' = 0
--                                 /\ pc' = [pc EXCEPT ![self] = "upgrade_drop_guard"]
--                            ELSE /\ pc' = [pc EXCEPT ![self] = "try_upgrade"]
--                                 /\ UNCHANGED << writer_lock,
--                                                 upgradeable_reader_lock,
--                                                 upgraded, reader_lock_count >>
--                      /\ UNCHANGED << role, stack, pre_val >>

-- upgrade_drop_guard(self) == /\ pc[self] = "upgrade_drop_guard"
--                             /\ Assert((upgradeable_reader_lock = TRUE),
--                                       "Failure of assertion at line 28, column 5 of macro called at line 159, column 9.")
--                             /\ upgradeable_reader_lock' = FALSE
--                             /\ role' = [role EXCEPT ![self] = WRITER]
--                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                             /\ UNCHANGED << writer_lock, upgraded,
--                                             reader_lock_count, pre_val >>

-- upgrade(self) == being_upgraded(self) \/ try_upgrade(self)
--                     \/ upgrade_drop_guard(self)

-- try_downgrade(self) == /\ pc[self] = "try_downgrade"
--                        /\ IF writer_lock /\ ~upgradeable_reader_lock /\ ~upgraded /\ reader_lock_count = 0
--                              THEN /\ upgradeable_reader_lock' = TRUE
--                                   /\ writer_lock' = FALSE
--                                   /\ upgraded' = FALSE
--                                   /\ reader_lock_count' = 0
--                                   /\ pc' = [pc EXCEPT ![self] = "downgrade_drop_guard"]
--                              ELSE /\ pc' = [pc EXCEPT ![self] = "try_downgrade"]
--                                   /\ UNCHANGED << writer_lock,
--                                                   upgradeable_reader_lock,
--                                                   upgraded, reader_lock_count >>
--                        /\ UNCHANGED << role, stack, pre_val >>

-- downgrade_drop_guard(self) == /\ pc[self] = "downgrade_drop_guard"
--                               /\ writer_lock' = FALSE
--                               /\ role' = [role EXCEPT ![self] = UPREADER]
--                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                               /\ UNCHANGED << upgradeable_reader_lock,
--                                               upgraded, reader_lock_count,
--                                               pre_val >>

-- downgrade(self) == try_downgrade(self) \/ downgrade_drop_guard(self)

-- start(self) == /\ pc[self] = "start"
--                /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "read",
--                                                               pc        |->  "may_change_role1" ] >>
--                                                           \o stack[self]]
--                      /\ pc' = [pc EXCEPT ![self] = "try_read"]
--                      /\ UNCHANGED pre_val
--                   \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "upread",
--                                                               pc        |->  "may_change_role1",
--                                                               pre_val   |->  pre_val[self] ] >>
--                                                           \o stack[self]]
--                      /\ pre_val' = [pre_val EXCEPT ![self] = defaultInitValue]
--                      /\ pc' = [pc EXCEPT ![self] = "try_upread"]
--                   \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "write",
--                                                               pc        |->  "may_change_role1" ] >>
--                                                           \o stack[self]]
--                      /\ pc' = [pc EXCEPT ![self] = "try_write"]
--                      /\ UNCHANGED pre_val
--                /\ UNCHANGED << writer_lock, upgradeable_reader_lock, upgraded,
--                                reader_lock_count, role >>

-- may_change_role1(self) == /\ pc[self] = "may_change_role1"
--                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "change_role",
--                                                                    pc        |->  "cs1" ] >>
--                                                                \o stack[self]]
--                           /\ pc' = [pc EXCEPT ![self] = "may_change_role"]
--                           /\ UNCHANGED << writer_lock, upgradeable_reader_lock,
--                                           upgraded, reader_lock_count, role,
--                                           pre_val >>

-- cs1(self) == /\ pc[self] = "cs1"
--              /\ TRUE
--              /\ pc' = [pc EXCEPT ![self] = "drop"]
--              /\ UNCHANGED << writer_lock, upgradeable_reader_lock, upgraded,
--                              reader_lock_count, role, stack, pre_val >>

-- drop(self) == /\ pc[self] = "drop"
--               /\ IF role[self] = READER
--                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_read",
--                                                                   pc        |->  "start" ] >>
--                                                               \o stack[self]]
--                          /\ pc' = [pc EXCEPT ![self] = "unlock_read"]
--                     ELSE /\ IF role[self] = WRITER
--                                THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_write",
--                                                                              pc        |->  "start" ] >>
--                                                                          \o stack[self]]
--                                     /\ pc' = [pc EXCEPT ![self] = "unlock_write"]
--                                ELSE /\ IF role[self] = UPREADER
--                                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_upgradeable",
--                                                                                         pc        |->  "start" ] >>
--                                                                                     \o stack[self]]
--                                                /\ pc' = [pc EXCEPT ![self] = "unlock_upgradeable"]
--                                           ELSE /\ Assert((FALSE),
--                                                          "Failure of assertion at line 226, column 13.")
--                                                /\ pc' = [pc EXCEPT ![self] = "start"]
--                                                /\ stack' = stack
--               /\ UNCHANGED << writer_lock, upgradeable_reader_lock, upgraded,
--                               reader_lock_count, role, pre_val >>

-- proc(self) == start(self) \/ may_change_role1(self) \/ cs1(self)
--                  \/ drop(self)

-- Next == (\E self \in ProcSet:  \/ change_role(self) \/ read(self)
--                                \/ drop_read(self) \/ write(self)
--                                \/ drop_write(self) \/ upread(self)
--                                \/ drop_upgradeable(self) \/ upgrade(self)
--                                \/ downgrade(self))
--            \/ (\E self \in Procs: proc(self))

-- Spec == /\ Init /\ [][Next]_vars
--         /\ \A self \in Procs : /\ WF_vars(proc(self))
--                                /\ WF_vars(read(self))
--                                /\ WF_vars(upread(self))
--                                /\ SF_vars(try_upread_check(self)) /\ SF_vars(try_upread_check_success(self))                               /\ WF_vars(write(self))
--                                /\ SF_vars(try_write(self))                               /\ WF_vars(change_role(self))
--                                /\ WF_vars(drop_read(self))
--                                /\ WF_vars(drop_write(self))
--                                /\ WF_vars(drop_upgradeable(self))
--                                /\ WF_vars(upgrade(self))
--                                /\ SF_vars(try_upgrade(self))                               /\ WF_vars(downgrade(self))
--                                /\ SF_vars(try_downgrade(self))

-- \* END TRANSLATION

-- IsWriterOrUpreader(i) == role[i] \in {WRITER, UPREADER}
-- OnlyOneWriterOrUpreader == \E i \in Procs: IsWriterOrUpreader(i) => (\A j \in Procs: (j /= i) => ~IsWriterOrUpreader(j))

-- IsInCS(i) == pc[i] \in {"cs1", "cs2"}
-- MutualExclusion == \E k \in Procs: (role[k] = WRITER) =>
--                         \A i, j \in Procs :
--                             (i # j) => ~ (IsInCS(i) /\ IsInCS(j))

-- Trying(i) == pc[i] \in {"try_read", "try_read_failed",
--                         "try_write",
--                         "try_upread", "try_upread_check", "try_upread_check_success",
--                         "being_upgraded", "try_upgrade", "upgrade_drop_guard"}

-- DeadAndLivelockFree == \E i \in Procs :
--                         Trying(i) ~> (\E j \in Procs : IsInCS(j))

-- StarvationFree == \A i \in Procs : Trying(i) ~> IsInCS(i)


-- =============================================================================
end rwlock
