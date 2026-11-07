\* Local TLC model for raft.tla (CC BY 4.0; see its header), with smaller instances than MC.tla.
\* raft.tla and MC.tla are copies of
\* https://github.com/jinlmsft/raft.tla/blob/76b4efab3bbd2a935d434cd364b294c443e90371/raft.tla and
\* .../raft.toolbox/Unique_Leader/MC.tla at the same commit. Like the upstream MC.cfg, the .cfg
\* files of this module bound the terms with the constraint of MC.tla.
---- MODULE MCSmall ----
EXTENDS raft, TLC

\* The sets of servers that the .cfg files choose from.
S1 == {"s1"}
S2 == {"s1", "s2"}
\* The servers of MC.tla.
S3 == {"s1", "s2", "s3"}

\* MC.tla's constr_1469115765473402000.
TermConstraint == \A i \in Server : currentTerm[i] < 3

\* MC.tla's inv_1469115765494404000 and inv_1469115765504405000.
NotMoreThanOneLeader == \lnot MoreThanOneLeader
NotCommittedLogDecrease == \lnot committedLogDecrease
====
