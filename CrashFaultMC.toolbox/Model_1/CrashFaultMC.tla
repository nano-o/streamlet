---------------------------- MODULE CrashFaultMC ----------------------------

EXTENDS FiniteSets, Naturals

CONSTANTS P, V
Quorum == {Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}

VARIABLES votes, chains, longest

INSTANCE CrashFault

BaitInv1 == \A v \in Vertices(chains) : Height(v) < 3
BaitInv2 == (\E v \in Vertices(chains) : Height(v) > 1 /\ Notarized(v)) 
    => \A v1,v2 \in Vertices(chains) : Reachable(v1,v2,chains) \/ Reachable(v2,v1,chains)
     

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 10:58:52 PST 2021 by nano
\* Created Fri Dec 17 10:14:38 PST 2021 by nano
