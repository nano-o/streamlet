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
const_16407590645291993000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_16407590645291994000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_16407590645291995000 == 
Permutations(const_16407590645291993000) \union Permutations(const_16407590645291994000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_16407590645291996000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:2GSE
const_16407590645291997000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4MaxEpoch
const_16407590645291998000 == 
5
----

=============================================================================
\* Modification History
\* Created Tue Dec 28 22:24:24 PST 2021 by nano
