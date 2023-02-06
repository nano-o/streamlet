---- MODULE MC ----
EXTENDS Streamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
TxSet1, TxSet2
----

\* MV CONSTANT definitions P
const_1675611843539469000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions TxSet
const_1675611843539470000 == 
{TxSet1, TxSet2}
----

\* SYMMETRY definition
symm_1675611843539471000 == 
Permutations(const_1675611843539469000) \union Permutations(const_1675611843539470000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1675611843539472000 == 
{{p1,p2},{p2,p3},{p3,p1}}
----

\* CONSTANT definitions @modelParameterConstants:2Leader(e)
const_1675611843539473000(e) == 
CASE e % 3 = 0 -> p1
[]	e % 3 = 1 -> p2
[]	e % 3 = 2 -> p3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1675611843539474000 ==
0..6
----
\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1675611843539475000 ==
\A p \in P : epoch'[p] <= 6
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1675611843539476000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Sun Feb 05 07:44:03 PST 2023 by nano
