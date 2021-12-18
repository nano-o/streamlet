---------------------------- MODULE CrashFaultMC ----------------------------

EXTENDS FiniteSets, Naturals

CONSTANTS P, V
Quorum == {Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}

VARIABLES votes, chains, notarizedHeight, votedHeight, marked

INSTANCE CrashFault

BaitInv1 == \neg \E v \in Vertices(chains) : 
    /\  Height(v) = 2 
    /\  Decided(v)
    /\  \E w \in Vertices(chains) : Height(w) = 1 /\ Notarized(w) /\ \neg Reachable(w,v,chains)
     

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 17:27:12 PST 2021 by nano
\* Created Fri Dec 17 10:14:38 PST 2021 by nano
