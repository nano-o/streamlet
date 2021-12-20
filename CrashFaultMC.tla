---------------------------- MODULE CrashFaultMC ----------------------------

EXTENDS FiniteSets, Naturals

CONSTANTS P, V
Quorum == {Q \in SUBSET P : 2*Cardinality(Q) > Cardinality(P)}

VARIABLES votes, height

INSTANCE CrashFault

BaitInv1 == \neg (\E v,w \in Vertices(G) : Height(v) = 1 /\ Notarized(v) /\ Height(w) = 3 /\ Notarized(w) /\ \neg Reachable(v,w,G))

=============================================================================
\* Modification History
\* Last modified Sun Dec 19 20:02:36 PST 2021 by nano
\* Created Fri Dec 17 10:14:38 PST 2021 by nano
