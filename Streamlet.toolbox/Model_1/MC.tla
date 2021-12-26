---- MODULE MC ----
EXTENDS Streamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5
----

\* MV CONSTANT definitions P
const_16402792182241488000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_16402792182241489000 == 
{v1, v2, v3, v4, v5}
----

\* SYMMETRY definition
symm_16402792182241490000 == 
Permutations(const_16402792182241488000) \union Permutations(const_16402792182241489000)
----

\* CONSTANT definitions @modelParameterConstants:2Round
const_16402792182241491000 == 
1..4
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16402792182241492000 == 
{Q\in SUBSET P: 2*Cardinality(Q)>Cardinality(P)}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_16402792182241493000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Thu Dec 23 09:06:58 PST 2021 by nano
