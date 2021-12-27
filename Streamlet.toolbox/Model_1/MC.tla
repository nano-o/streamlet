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
const_16406475080911384000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_16406475080911385000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_16406475080911386000 == 
Permutations(const_16406475080911384000) \union Permutations(const_16406475080911385000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_16406475080911387000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:3MaxEpoch
const_16406475080911388000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4GSE
const_16406475080911389000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_16406475080911390000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Mon Dec 27 15:25:08 PST 2021 by nano
