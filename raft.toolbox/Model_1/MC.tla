---- MODULE MC ----
EXTENDS raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Server
const_158591100545364000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:8Value
const_158591100545365000 == 
{1}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158591100545366000 ==
/\ \A i \in Server:currentTerm[i]<3
/\ \A i \in Server:Len(log[i]) < 3
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_158591100545467000 ==
\lnot MoreThanOneLeader
----
=============================================================================
\* Modification History
\* Created Fri Apr 03 18:50:05 CST 2020 by jason
