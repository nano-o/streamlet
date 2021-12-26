---- MODULE MC ----
EXTENDS SynchronousStreamletLiveness2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Tx
const_16405561335732000 == 
{Tx1, Tx2}
----

\* MV CONSTANT definitions P
const_16405561335733000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_16405561335734000 == 
Permutations(const_16405561335732000) \union Permutations(const_16405561335733000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxEpoch
const_16405561335735000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16405561335736000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:4GSE
const_16405561335737000 == 
3
----

=============================================================================
\* Modification History
\* Created Sun Dec 26 14:02:13 PST 2021 by nano
