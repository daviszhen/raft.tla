---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585989272030110000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585989272030111000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585989272030112000 ==
\A i \in Server: 
currentTerm[i] < 2
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585989272030113000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585989272030114000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:34:32 CST 2020 by jason
