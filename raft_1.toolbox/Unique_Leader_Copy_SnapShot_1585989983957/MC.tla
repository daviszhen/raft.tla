---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585989980884145000 == 
{"s1"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585989980884146000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585989980884147000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585989980884148000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585989980884149000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:46:20 CST 2020 by jason
