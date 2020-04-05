---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585989668204135000 == 
{"s1","s2"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585989668204136000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585989668204137000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585989668204138000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1585989668204139000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 16:41:08 CST 2020 by jason
