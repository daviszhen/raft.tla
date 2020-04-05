---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_158598919399795000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_158598919399796000 == 
1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158598919399797000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158598919399898000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_158598919399899000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:33:13 CST 2020 by jason
