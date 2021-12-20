----------------------------- MODULE Streamlet -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, DiGraph, TLC, FiniteSets

CONSTANTS
        P \* The set of processors
    ,   V \* The set of values
    ,   Quorum \* The set of quorums
    ,   Round \* The set of rounds. Should be of the form 0..N

ChainRoot == CHOOSE v \in V : TRUE \* An arbitrary vertice

Max(E) == CHOOSE e \in E : \A f \in E : f <= e

(* 
--algorithm Streamlet {
    variables
        chains = <<{ChainRoot}, {}>>, \* the digraph formed by the nodes' votes
        vote = [p \in P |-> [r \in Round \ {0} |-> <<>>]], \* the votes cast by the processes
    define {
        Notarized(v,r) ==
            \/  (v = ChainRoot /\ r = 0) 
            \/  /\  r > 0 /\ v \in V 
                /\  \E Q \in Quorum : \A p \in Q : vote[p][r] = v 
        Height(v) == Distance({ChainRoot}, v, chains)
        (*******************************************************************)
        (* By Inv1, we know that if a tip is more than on behind, it can   *)
        (* never be built on anymore.  So we can decide when we detect     *)
        (* that all competing tips must be more than one behind.  This is  *)
        (* when two vertices are notarized in a row.                       *)
        (*******************************************************************)
        \* Decided vertices:
        Decided(v) == \E v1,v3 \in V : \E r \in Round : 
            /\  r+2 <= Max(Round)
            /\  Notarized(v1,r) /\  Notarized(v,r+1) /\  Notarized(v3,r+2)
            /\  v \in Children({v1}, chains) /\ v3 \in Children({v}, chains) 
        \* Main safety property:
        Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Compatible(w, v, chains)
        BaitInv1 == \A v \in V : \neg Decided(v)
    }
    process (proc \in P)
        variables 
            round = 1, \* current round 
            height = 0, \* height of the longest notarized chain seen so far
    {
l1:     while (TRUE) { \* extend a longer notarized chain with a vote and go to the next round
            when round \in Round; \* for TLC            
                with (v \in Vertices(chains)) { \* the notarized vertice we're going to extend
                    when Height(v) >= height /\ \E r \in Round : r < round /\ Notarized(v,r);
                    with (w \in (V \ Vertices(chains)) \cup Children({v}, chains)) { \* pick a fresh vertice or vote for an existing child of v
                        chains := AddEdge(v, w, chains);
                        vote[self][round] := w;
                    };
                    height := Height(v);
                    round := round +1;
                }
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a8cac0b4" /\ chksum(tla) = "5303f4ee")
VARIABLES chains, vote

(* define statement *)
Notarized(v,r) ==
    \/  (v = ChainRoot /\ r = 0)
    \/  /\  r > 0 /\ v \in V
        /\  \E Q \in Quorum : \A p \in Q : vote[p][r] = v
Height(v) == Distance({ChainRoot}, v, chains)







Decided(v) == \E v1,v3 \in V : \E r \in Round :
    /\  r+2 <= Max(Round)
    /\  Notarized(v1,r) /\  Notarized(v,r+1) /\  Notarized(v3,r+2)
    /\  v \in Children({v1}, chains) /\ v3 \in Children({v}, chains)

Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Compatible(w, v, chains)
BaitInv1 == \A v \in V : \neg Decided(v)

VARIABLES round, height

vars == << chains, vote, round, height >>

ProcSet == (P)

Init == (* Global variables *)
        /\ chains = <<{ChainRoot}, {}>>
        /\ vote = [p \in P |-> [r \in Round \ {0} |-> <<>>]]
        (* Process proc *)
        /\ round = [self \in P |-> 1]
        /\ height = [self \in P |-> 0]

proc(self) == /\ round[self] \in Round
              /\ \E v \in Vertices(chains):
                   /\ Height(v) >= height[self] /\ \E r \in Round : r < round[self] /\ Notarized(v,r)
                   /\ \E w \in (V \ Vertices(chains)) \cup Children({v}, chains):
                        /\ chains' = AddEdge(v, w, chains)
                        /\ vote' = [vote EXCEPT ![self][round[self]] = w]
                   /\ height' = [height EXCEPT ![self] = Height(v)]
                   /\ round' = [round EXCEPT ![self] = round[self] +1]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Dec 19 19:17:49 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
