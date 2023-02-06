---- MODULE MC ----
EXTENDS SequentializedStreamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Tx
const_1675660808823486000 == 
{Tx1, Tx2}
----

\* MV CONSTANT definitions P
const_1675660808823487000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1675660808823488000 == 
Permutations(const_1675660808823486000)
----

\* CONSTANT definitions @modelParameterConstants:0GSE
const_1675660808823489000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_1675660808823490000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:4Leader(e)
const_1675660808823491000(e) == 
CASE e % 3 = 0 -> p1
[]	e % 3 = 1 -> p2
[]	e % 3 = 2 -> p3
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1675660808823492000 ==
epoch < 9
----
=============================================================================
\* Modification History
\* Created Sun Feb 05 21:20:08 PST 2023 by nano
