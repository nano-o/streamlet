---- MODULE MC ----
EXTENDS CrashFaultMC, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5, v6
----

\* MV CONSTANT definitions P
const_16399732840901279000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_16399732840901280000 == 
{v1, v2, v3, v4, v5, v6}
----

\* SYMMETRY definition
symm_16399732840901281000 == 
Permutations(const_16399732840901279000) \union Permutations(const_16399732840901280000)
----

=============================================================================
\* Modification History
\* Created Sun Dec 19 20:08:04 PST 2021 by nano
