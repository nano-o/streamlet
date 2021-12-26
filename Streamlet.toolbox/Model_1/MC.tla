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
const_164055967818276000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_164055967818277000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_164055967818278000 == 
Permutations(const_164055967818276000) \union Permutations(const_164055967818277000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_164055967818279000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:3MaxEpoch
const_164055967818280000 == 
4
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_164055967818381000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Sun Dec 26 15:01:18 PST 2021 by nano
