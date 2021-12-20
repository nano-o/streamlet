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
const_163997681310784000 == 
{v1, v2, v3, v4, v5}
----

\* MV CONSTANT definitions P
const_163997681310785000 == 
{p1, p2, p3}
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_163997681310786000 == 
{Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}
----

=============================================================================
\* Modification History
\* Created Sun Dec 19 21:06:53 PST 2021 by nano
