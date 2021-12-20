---- MODULE MC ----
EXTENDS CrashFault, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions V
const_1639978218258140000 == 
{v1, v2, v3, v4, v5}
----

\* MV CONSTANT definitions P
const_1639978218258141000 == 
{p1, p2, p3}
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_1639978218258142000 == 
{Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}
----

=============================================================================
\* Modification History
\* Created Sun Dec 19 21:30:18 PST 2021 by nano
