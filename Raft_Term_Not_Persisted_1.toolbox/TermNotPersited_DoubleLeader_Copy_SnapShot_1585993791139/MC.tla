---- MODULE MC ----
EXTENDS Raft_Term_Not_Persisted, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_15860831954327000 == 
{ "s1", "s2", "s3" }
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_15860831954328000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10LossyNetwork
const_15860831954329000 == 
FALSE
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158608319543210000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158608319543211000 ==
\lnot MoreThanOneLeader
----
=============================================================================
\* Modification History
\* Created Sun Apr 05 18:39:55 CST 2020 by jason
