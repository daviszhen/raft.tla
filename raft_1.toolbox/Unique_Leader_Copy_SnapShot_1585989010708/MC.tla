---- MODULE MC ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:8Server
const_158598532236345000 == 
{"s1","s2","s3"}
----

\* CONSTANT definitions @modelParameterConstants:9MaxClientRequests
const_158598532236346000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158598532236347000 ==
\A i \in Server: 
currentTerm[i] < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158598532236348000 ==
\lnot MoreThanOneLeader
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_158598532236349000 ==
\lnot committedLogDecrease
----
=============================================================================
\* Modification History
\* Created Sat Apr 04 15:28:42 CST 2020 by jason
