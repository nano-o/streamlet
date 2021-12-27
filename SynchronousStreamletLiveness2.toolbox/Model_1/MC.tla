---- MODULE MC ----
EXTENDS SynchronousStreamletLiveness2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Tx1, Tx2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Tx
const_16406471582701368000 == 
{Tx1, Tx2}
----

\* MV CONSTANT definitions P
const_16406471582701369000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_16406471582701370000 == 
Permutations(const_16406471582701368000) \union Permutations(const_16406471582701369000)
----

\* New definitions @modelParameterNewDefinitions
State1 ==
/\  epoch = 3
/\  height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 1)
/\  n = 2
/\  proposal = <<<<3, Tx1>>>>
/\  votes = ( p1 :> {<<<<1, Tx1>>>>, <<<<2, Tx1>>>>, <<<<3, Tx1>>>>} @@
  p2 :> {<<<<1, Tx1>>>>, <<<<1, Tx1>>, <<2, Tx1>>>>} @@
  p3 :> {<<<<1, Tx1>>>>, <<<<1, Tx1>>, <<2, Tx1>>>>} )
----
\* CONSTANT definitions @modelParameterConstants:0MaxEpoch
const_16406471582701371000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:3Quorum
const_16406471582701372000 == 
{{p1,p2},{p2,p3}}
----

\* CONSTANT definitions @modelParameterConstants:4GSE
const_16406471582701373000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_16406471582701374000 ==
Init /\ [][Next]_vars
----
=============================================================================
\* Modification History
\* Created Mon Dec 27 15:19:18 PST 2021 by nano
