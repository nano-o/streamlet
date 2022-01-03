---- MODULE MC ----
EXTENDS SynchronousStreamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT definitions P
const_1641184444247611000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_1641184444247612000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_1641184444247613000 == 
Permutations(const_1641184444247611000) \union Permutations(const_1641184444247612000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1641184444247614000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:2GSE
const_1641184444247615000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4MaxEpoch
const_1641184444247616000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:5Leader(e)
const_1641184444247617000(e) == 
CASE e % 3 = 0 -> p1
[]	e % 3 = 1 -> p2
[]	e % 3 = 2 -> p3
----

=============================================================================
\* Modification History
\* Created Sun Jan 02 20:34:04 PST 2022 by nano
