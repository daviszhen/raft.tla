---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Value
const_158597644468795000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:9Server
const_158597644468796000 == 
{"a1", "a2", "a3"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158597644468797000 ==
/\ \A i \in Server:currentTerm[i]<3
/\ clientRequests < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158597644468898000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_158597644468899000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 13:00:44 CST 2020 by jason
