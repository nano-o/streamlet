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
const_1641168032215361000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_1641168032215362000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_1641168032215363000 == 
Permutations(const_1641168032215361000) \union Permutations(const_1641168032215362000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1641168032215364000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:3MaxEpoch
const_1641168032215365000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4Leader(e)
const_1641168032215366000(e) == 
CASE e % 3 = 0 -> p1
[]	e % 3 = 1 -> p2
[]	e % 3 = 2 -> p3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1641168032215367000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Sun Jan 02 16:00:32 PST 2022 by nano
