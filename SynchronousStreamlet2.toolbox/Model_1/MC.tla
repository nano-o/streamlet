---- MODULE MC ----
EXTENDS SynchronousStreamlet2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
tx1, tx2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Tx
const_16403027992361538000 == 
{tx1, tx2}
----

\* MV CONSTANT definitions P
const_16403027992361539000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_16403027992361540000 == 
Permutations(const_16403027992361538000) \union Permutations(const_16403027992361539000)
----

\* CONSTANT definitions @modelParameterConstants:1E
const_16403027992361541000 == 
1..4
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16403027992361542000 == 
{Q \in SUBSET P : 2*Cardinality(Q)>Cardinality(P)}
----

=============================================================================
\* Modification History
\* Created Thu Dec 23 15:39:59 PST 2021 by nano
