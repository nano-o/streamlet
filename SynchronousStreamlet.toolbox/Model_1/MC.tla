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
const_1641164566513345000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_1641164566513346000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_1641164566513347000 == 
Permutations(const_1641164566513345000) \union Permutations(const_1641164566513346000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1641164566513348000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:2GSE
const_1641164566513349000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:4MaxEpoch
const_1641164566513350000 == 
6
----

=============================================================================
\* Modification History
\* Created Sun Jan 02 15:02:46 PST 2022 by nano
