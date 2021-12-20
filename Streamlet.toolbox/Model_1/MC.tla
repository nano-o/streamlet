---- MODULE MC ----
EXTENDS Streamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5, v6, v7
----

\* MV CONSTANT definitions P
const_16399704366431032000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_16399704366431033000 == 
{v1, v2, v3, v4, v5, v6, v7}
----

\* SYMMETRY definition
symm_16399704366431034000 == 
Permutations(const_16399704366431032000) \union Permutations(const_16399704366431033000)
----

\* CONSTANT definitions @modelParameterConstants:2Round
const_16399704366431035000 == 
0..4
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16399704366431036000 == 
{Q\in SUBSET P: 2*Cardinality(Q)>Cardinality(P)}
----

=============================================================================
\* Modification History
\* Created Sun Dec 19 19:20:36 PST 2021 by nano
