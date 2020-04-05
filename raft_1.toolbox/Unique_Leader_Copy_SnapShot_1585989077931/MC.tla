---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_158598907480060000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_158598907480061000 == 
1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158598907480062000 ==
\A i \in Server: 
currentTerm[i] < 2
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158598907480063000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_158598907480064000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:31:14 CST 2020 by jason
