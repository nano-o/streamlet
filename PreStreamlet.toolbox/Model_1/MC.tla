---- MODULE MC ----
EXTENDS PreStreamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5, v6
----

\* MV CONSTANT definitions P
const_1640018388698303000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_1640018388698304000 == 
{v1, v2, v3, v4, v5, v6}
----

\* New definitions @modelParameterNewDefinitions
MyInit == 
/\ height = (p1 :> 0 @@ p2 :> 0 @@ p3 :> 0)
/\ votes = (p1 :> {<<v1, v3>>, <<v1, v5>>} @@ p2 :> {<<v1, v3>>} @@ p3 :> {<<v1, v5>>})
----
\* CONSTANT definitions @modelParameterConstants:2Quorum
const_1640018388698305000 == 
{Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1640018388699306000 ==
MyInit /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Mon Dec 20 08:39:48 PST 2021 by nano
