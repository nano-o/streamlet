----------------------------- MODULE Streamlet -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets

CONSTANTS
        P \* The set of processors
    ,   V \* The set of values
    ,   Quorum \* The set of quorums
    ,   Round \* The set of rounds. Should be of the form 1..N

(***************************************************************************)
(* First we need a few notions about directed graphs.  A directed graph is *)
(* a set of edges.                                                         *)
(***************************************************************************)

Vertices(G) == {v \in V : \E w \in V : <<v,w>> \in G \/ <<w,v>> \in G}

IsDigraph(G) == \A e \in G : e[1] \in Vertices(G) /\ e[2] \in Vertices(G) 
    
Children(W, G) == UNION {{w \in Vertices(G) : <<v,w>> \in G} : v \in W} 
            
RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, G) == \* CAUTION: does not terminate if there is a cycle reachable from v1
    \/  v1 = v2
    \/  <<v1,v2>> \in G
    \/  \E v3 \in Children({v1}, G) : Reachable(v3, v2, G)
        
Compatible(v, w, G) == Reachable(v, w, G) \/ Reachable(w, v, G)

RECURSIVE Distance(_,_,_)
Distance(W, v, G) == \* W is a set of vertices
    CASE
        v \in W -> 0
    []  v \in Children(W,G) -> 1
    []  OTHER -> 1 + Distance(Children(W,G), v, G)
    
 
(***************************************************************************)
(* Now we're ready for the algorithm.                                      *)
(*                                                                         *)
(* We want to show that the height of two competing tips differ at most by *)
(* 1.                                                                      *)
(***************************************************************************)

Root == CHOOSE v \in V : TRUE

Max(E) == CHOOSE e \in E : \A f \in E : f <= e

(****************************************************************************
Error trace

Reachable (use 4 rounds, values {v1,v2,v3,v5}, and _no symmetry reduction_):

    Bait1 ==
    /\  height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
    /\  round = (p1 :> 4 @@ p2 :> 3 @@ p3 :> 4)
    /\  votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1,v5>>, <<>>, <<>>, <<>>>> @@
      p2 :> <<<<v1, v3>>, <<v3,v2>>, <<>>, <<>>, <<>>, <<>>>> @@
      p3 :> <<<<>>, <<>>, <<v1,v5>>, <<>>, <<>>, <<>>>> )
      
Reachable? (use 5 rounds, values {v1,v2,v3,v4,v5,v6}, and symmetry is okay:

    \neg Safety
      
****************************************************************************)


(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> [r \in Round |-> <<>>]], \* the votes cast by the processes
    define {
        G == {votes[p][r] : p \in P, r \in Round} \ {<<>>}
        Notarized(r,v) == 
            IF r = 0
            THEN v = Root
            ELSE \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : votes[p][r] = <<w,v>>
        Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)
        (*******************************************************************)
        (* By Inv1, we know that if a tip is more than on behind, it can   *)
        (* never be built on anymore.  So we can decide when we detect     *)
        (* that all competing tips must be more than one behind.  This is  *)
        (* when two vertices are notarized in a row.                       *)
        (*******************************************************************)
        \* Decided vertices:
        Decided(v) == \E v1,v3 \in V : \E r \in Round \cup {0}: 
            /\  r+2 <= Max(Round)
            /\  Notarized(r,v1) /\  Notarized(r+1,v) /\  Notarized(r+2,v3)
            /\  v \in Children({v1}, G) /\ v3 \in Children({v}, G) 
        \* Main safety property:
        Safety == \A v,w \in Vertices(G) : Decided(v) /\ Decided(w) => Compatible(w, v, G)
        BaitInv1 == \A v \in V : \neg Decided(v)
    }
    process (proc \in P)
        \*variables 
            \*round = 1, \* current round
    {
l1:     while (TRUE) { 
            \* when round \in Round; \* for TLC            
            either { \* extend a longer notarized chain with a vote
                with (round \in {r \in Round : votes[self][r] = <<>>})
                with (v \in Vertices(G) \cup {Root}) { \* the notarized vertice we're going to extend
                    when Height(v) >= height[self] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,v);
                    with (w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G)) { \* pick a fresh vertice or vote for an existing child of v
                        votes[self][round] := <<v,w>>;
                    };
                    height[self] := Height(v);
                };
            } or { \* skip the round
                skip;
            };
            \*round := round +1; \* go to the next round
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "23044fd" /\ chksum(tla) = "562132e3")
VARIABLES height, votes

(* define statement *)
G == {votes[p][r] : p \in P, r \in Round} \ {<<>>}
Notarized(r,v) ==
    IF r = 0
    THEN v = Root
    ELSE \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : votes[p][r] = <<w,v>>
Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)







Decided(v) == \E v1,v3 \in V : \E r \in Round \cup {0}:
    /\  r+2 <= Max(Round)
    /\  Notarized(r,v1) /\  Notarized(r+1,v) /\  Notarized(r+2,v3)
    /\  v \in Children({v1}, G) /\ v3 \in Children({v}, G)

Safety == \A v,w \in Vertices(G) : Decided(v) /\ Decided(w) => Compatible(w, v, G)
BaitInv1 == \A v \in V : \neg Decided(v)


vars == << height, votes >>

ProcSet == (P)

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> [r \in Round |-> <<>>]]

proc(self) == \/ /\ \E round \in {r \in Round : votes[self][r] = <<>>}:
                      \E v \in Vertices(G) \cup {Root}:
                        /\ Height(v) >= height[self] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,v)
                        /\ \E w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G):
                             votes' = [votes EXCEPT ![self][round] = <<v,w>>]
                        /\ height' = [height EXCEPT ![self] = Height(v)]
              \/ /\ TRUE
                 /\ UNCHANGED <<height, votes>>

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Dec 20 14:25:24 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
