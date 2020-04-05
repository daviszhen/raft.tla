---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585990235881155000 == 
{"s1","s2"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585990235881156000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585990235881157000 ==
\A i \in Server: 
currentTerm[i] < 2
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585990235882158000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585990235882159000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:50:35 CST 2020 by jason
