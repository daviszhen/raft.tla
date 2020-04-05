---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_158598918111785000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_158598918111786000 == 
1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158598918111787000 ==
\A i \in Server: 
currentTerm[i] < 2
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158598918111788000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_158598918111789000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:33:01 CST 2020 by jason
