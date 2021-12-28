---- MODULE MC ----
EXTENDS SynchronousStreamlet, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT definitions P
const_16406477924831408000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Tx
const_16406477924831409000 == 
{Tx1, Tx2}
----

\* SYMMETRY definition
symm_16406477924831410000 == 
Permutations(const_16406477924831408000) \union Permutations(const_16406477924831409000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_16406477924831411000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:2GSE
const_16406477924831412000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4MaxEpoch
const_16406477924831413000 == 
6
----

=============================================================================
\* Modification History
\* Created Mon Dec 27 15:29:52 PST 2021 by nano
