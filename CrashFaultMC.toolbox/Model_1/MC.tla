---- MODULE MC ----
EXTENDS CrashFaultMC, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4, v5, v6, v7, v8
----

\* MV CONSTANT definitions P
const_1639768087211271000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions V
const_1639768087211272000 == 
{v1, v2, v3, v4, v5, v6, v7, v8}
----

\* SYMMETRY definition
symm_1639768087211273000 == 
Permutations(const_1639768087211271000)
----

=============================================================================
\* Modification History
\* Created Fri Dec 17 11:08:07 PST 2021 by nano
