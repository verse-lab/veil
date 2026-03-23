---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1469115765452400000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1469115765463401000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1469115765473402000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1469115765483403000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1469115765494404000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1469115765504405000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Thu Jul 21 08:42:45 PDT 2016 by jinl
