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
const_16403051401821687000 == 
{tx1, tx2}
----

\* MV CONSTANT definitions P
const_16403051401821688000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_16403051401821689000 == 
Permutations(const_16403051401821687000) \union Permutations(const_16403051401821688000)
----

\* CONSTANT definitions @modelParameterConstants:1E
const_16403051401821690000 == 
1..4
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16403051401821691000 == 
{Q \in SUBSET P : 2*Cardinality(Q)>Cardinality(P)}
----

=============================================================================
\* Modification History
\* Created Thu Dec 23 16:19:00 PST 2021 by nano
