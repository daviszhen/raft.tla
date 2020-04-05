---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585990387417175000 == 
{"s1","s2"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585990387417176000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585990387417177000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585990387417178000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585990387417179000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:53:07 CST 2020 by jason
