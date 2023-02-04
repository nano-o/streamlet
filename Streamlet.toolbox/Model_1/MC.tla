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
const_1675537902977684000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_1675537902977685000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_1675537902977686000 == 
Permutations(const_1675537902977684000) \union Permutations(const_1675537902977685000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1675537902977687000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:3Leader(e)
const_1675537902977688000(e) == 
CASE e % 3 = 0 -> p1
[]	e % 3 = 1 -> p2
[]	e % 3 = 2 -> p3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1675537902977689000 ==
0..6
----
\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_1675537902977690000 ==
\A p \in P : epoch'[p] <= 6
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1675537902977691000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Sat Feb 04 11:11:42 PST 2023 by nano
