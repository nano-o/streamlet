---- MODULE MC ----
EXTENDS Streamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5, v6
----

\* MV CONSTANT definitions P
const_1640022420505539000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_1640022420505540000 == 
{v1, v2, v3, v4, v5, v6}
----

\* SYMMETRY definition
symm_1640022420505541000 == 
Permutations(const_1640022420505539000) \union Permutations(const_1640022420505540000)
----

\* New definitions @modelParameterNewDefinitions
MyInit == 
/\  height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\  round = (p1 :> 4 @@ p2 :> 3 @@ p3 :> 4)
/\  votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1,v5>>, <<>>, <<>>>> @@
  p2 :> <<<<v1, v3>>, <<v3,v2>>, <<>>, <<>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1,v5>>, <<>>, <<>>>> )
----
\* CONSTANT definitions @modelParameterConstants:2Round
const_1640022420505542000 == 
1..5
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_1640022420505543000 == 
{Q\in SUBSET P: 2*Cardinality(Q)>Cardinality(P)}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1640022420505544000 ==
MyInit /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Mon Dec 20 09:47:00 PST 2021 by nano
