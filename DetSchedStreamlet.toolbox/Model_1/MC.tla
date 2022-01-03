---- MODULE MC ----
EXTENDS DetSchedStreamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
tx1, tx2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Tx
const_1641189080613796000 == 
{tx1, tx2}
----

\* MV CONSTANT definitions P
const_1641189080613797000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1641189080613798000 == 
Permutations(const_1641189080613796000) \union Permutations(const_1641189080613797000)
----

\* CONSTANT definitions @modelParameterConstants:0GSE
const_1641189080613799000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_1641189080613800000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:4MaxEpoch
const_1641189080613801000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:5Leader(e)
const_1641189080613802000(e) == 
CASE e % 3 = 0 -> p1
[] e % 3 = 1 -> p2
[] e % 3 = 2 -> p3
----

=============================================================================
\* Modification History
\* Created Sun Jan 02 21:51:20 PST 2022 by nano
