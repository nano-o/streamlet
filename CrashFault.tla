----------------------------- MODULE CrashFault -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Naturals

CONSTANTS
        P \* processors
    ,   V \* values

(***************************************************************************)
(* We need to reason about directed graphs, and trees in particular.  A    *)
(* digraph consists of edges and vertices.                                 *)
(***************************************************************************)
Vertices(G) == G[1]
Edges(G) == G[2]
IsDigraph(G) ==
    /\  G = <<Vertices(G), Edges(G)>>
    /\  Edges(G) \subseteq (Vertices(G) \times Vertices(G))
    
Children(W, G) == UNION {{w \in Vertices(G) : <<v,w>> \in Edges(G)} : v \in W} 

RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, G) ==
    /\  v1 \in Vertices(G) /\ v2 \in Vertices(G)
    /\  \/  v1 = v2
        \/  <<v1,v2>> \in Edges(G)
        \/  \E v3 \in Children({v1}, G) : Reachable(v3, v2, G)
        
RECURSIVE ReachableSet(_,_)
 ReachableSet(W,G) == \* W is a set of vertices
    LET C == Children(W, G) IN 
        IF C = {}
        THEN W
        ELSE W \cup {ReachableSet(C,G)}

RECURSIVE Distance(_,_,_)
Distance(W, v, G) == \* W is a set of vertices
    CASE
        v \in W -> 0
    []  v \in Children(W,G) -> 1
    []  OTHER -> 1 + Distance(Children(W,G), v, G)
    
 
(***************************************************************************)
(* Now we're ready for the algorithm                                       *)
(***************************************************************************)

ChainRoot == CHOOSE v \in V : TRUE \* we pick an arbitrary root

CONSTANT Quorum

(* 
--algorithm Consensus {
    variables
        digraph = <<{ChainRoot}, {}>>, \* invariant: will remain a tree
        longest = [p \in P |-> ChainRoot], \* longest notarized chain known to p
        votes = [p \in P |-> {}] \* processes vote for digraph vertices
    define {
        Notarized(v) == \E Q \in Quorum : \A p \in Q : v \in votes[p]   
        Height(v) == Distance(ChainRoot, v, digraph)
        AddEdge(v, w, g) ==
            LET Vs == Vertices(g) \cup {v}
                Es == Edges(g) \cup <<v,w>> 
            IN <<Vs, Es>>
    }
    process (proc \in P) {
l1:     \* extend a longer notarized chain with a vote
        while (TRUE)
            with (v \in Vertices(digraph)) {
                when Notarized(v) /\ Height(v) >= Height(longest[self]);
                when \A w \in V : \neg (w \in Children(v, digraph) /\ w \in votes[self]); \* not extended v yet
                with (w \in (V \ Vertices(digraph)) \cup Children(v, digraph)) { \* pick a fresh vertice or vote for an exiting child
                    longest[self] := v; 
                    digraph := AddEdge(v, w, digraph);
                    votes[self] := votes[self] \cup w;
                }
            }
        }
    }
}  
*)
\* BEGIN TRANSLATION (chksum(pcal) = "49a66ddd" /\ chksum(tla) = "76624dc1")
VARIABLES digraph, longest, votes

(* define statement *)
Notarized(v) == \E Q \in Quorum : \A p \in Q : v \in votes[p]
Height(v) == Distance(ChainRoot, v, digraph)
AddEdge(v, w, g) ==
    LET Vs == Vertices(g) \cup {v}
        Es == Edges(g) \cup <<v,w>>
    IN <<Vs, Es>>


vars == << digraph, longest, votes >>

ProcSet == (P)

Init == (* Global variables *)
        /\ digraph = <<{ChainRoot}, {}>>
        /\ longest = [p \in P |-> ChainRoot]
        /\ votes = [p \in P |-> {}]

proc(self) == \E v \in Vertices(digraph):
                /\ Notarized(v) /\ Height(v) >= Height(longest[self])
                /\ \A w \in V : \neg (w \in Children(v, digraph) /\ w \in votes[self])
                /\ \E w \in (V \ Vertices(digraph)) \cup Children(v, digraph):
                     /\ longest' = [longest EXCEPT ![self] = v]
                     /\ digraph' = AddEdge(v, w, digraph)
                     /\ votes' = [votes EXCEPT ![self] = votes[self] \cup w]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 09:23:15 PST 2021 by nano
\* Created Fri Dec 17 07:53:09 PST 2021 by nano
