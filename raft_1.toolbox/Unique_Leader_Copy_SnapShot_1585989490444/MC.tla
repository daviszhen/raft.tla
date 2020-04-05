---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585989452988125000 == 
{"s1","s2"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585989452988126000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585989452988127000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585989452989128000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585989452989129000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:37:32 CST 2020 by jason
