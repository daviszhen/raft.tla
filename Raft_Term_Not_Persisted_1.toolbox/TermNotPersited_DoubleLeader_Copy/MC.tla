---- MODULE MC ----
EXTENDS Raft_Term_Not_Persisted, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_1585993647115185000 == 
{ "s1", "s2", "s3" }
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_1585993647115186000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10LossyNetwork
const_1585993647115187000 == 
FALSE
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1585993647115188000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1585993647115189000 ==
\lnot MoreThanOneLeader
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 17:47:27 CST 2020 by jason
