---- MODULE MC ----
EXTENDS Streamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT definitions P
const_16407593006262018000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_16407593006262019000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_16407593006262020000 == 
Permutations(const_16407593006262018000) \union Permutations(const_16407593006262019000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_16407593006262021000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:3MaxEpoch
const_16407593006262022000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4GSE
const_16407593006262023000 == 
5
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_16407593006262024000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Tue Dec 28 22:28:20 PST 2021 by nano
