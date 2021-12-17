----------------------------- MODULE CrashFault -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Naturals, TLC

CONSTANTS
        P \* processors
    ,   V \* values
    ,   Quorum \* Quorums

(***************************************************************************)
(* We need to reason about directed graphs, and trees in particular.  A    *)
(* chains consists of edges and vertices.                                 *)
(***************************************************************************)
Vertices(G) == G[1]
Edges(G) == G[2]
IsDigraph(G) ==
    /\  G = <<Vertices(G), Edges(G)>>
    /\  Edges(G) \subseteq (Vertices(G) \times Vertices(G))
    
Children(W, G) == UNION {{w \in Vertices(G) : <<v,w>> \in Edges(G)} : v \in W} 

AddEdge(v, w, G) ==
    LET Vs == Vertices(G) \cup {w}
        Es == Edges(G) \cup {<<v,w>>} 
    IN <<Vs, Es>>
            
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
(* Now we're ready for the algorithm.                                      *)
(*                                                                         *)
(* The main invariant is that a node has at most on notarized child.  By   *)
(* induction from the root, this means there's a single notarized chain.   *)
(***************************************************************************)

ChainRoot == CHOOSE v \in V : TRUE \* we pick an arbitrary root

(* 
--algorithm Consensus {
    variables
        chains = <<{ChainRoot}, {}>>, \* invariant: will remain a tree
        longest = [p \in P |-> ChainRoot], \* longest notarized chain known to p
        votes = [p \in P |-> {}] \* processes vote for chains vertices
    define {
        Notarized(v) == \E Q \in Quorum : \A p \in Q : v \in votes[p]   
        Height(v) == Distance({ChainRoot}, v, chains)
        Decided(v) == v \in Vertices(chains) /\ \E w \in Children({v}, chains) : Notarized(w)
        Inv1 == \A v \in Vertices(chains) : \A w1,w2 \in Children({v}, chains) : Notarized(w1) /\ Notarized(w2) => w1 = w2
        Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Reachable(v, w, chains) \/ Reachable(w, v, chains)
    }
    process (proc \in P) {
l1:     \* extend a longer notarized chain with a vote
        while (TRUE)
            with (v \in Vertices(chains)) {
                when (Notarized(v) \/ v = ChainRoot) /\ Height(v) >= Height(longest[self]);
                longest[self] := v;
                when \A w \in V : \neg (w \in Children({v}, chains) /\ w \in votes[self]); \* not extended v yet
                with (w \in (V \ Vertices(chains)) \cup Children({v}, chains)) { \* pick a fresh vertice or vote for an exiting child
                    chains := AddEdge(v, w, chains);
                    votes[self] := votes[self] \cup {w};
                }
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b2e7420a" /\ chksum(tla) = "eadecc7e")
VARIABLES chains, longest, votes

(* define statement *)
Notarized(v) == \E Q \in Quorum : \A p \in Q : v \in votes[p]
Height(v) == Distance({ChainRoot}, v, chains)
Decided(v) == v \in Vertices(chains) /\ \E w \in Children({v}, chains) : Notarized(w)
Inv1 == \A v \in Vertices(chains) : \A w1,w2 \in Children({v}, chains) : Notarized(w1) /\ Notarized(w2) => w1 = w2
Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Reachable(v, w, chains) \/ Reachable(w, v, chains)


vars == << chains, longest, votes >>

ProcSet == (P)

Init == (* Global variables *)
        /\ chains = <<{ChainRoot}, {}>>
        /\ longest = [p \in P |-> ChainRoot]
        /\ votes = [p \in P |-> {}]

proc(self) == \E v \in Vertices(chains):
                /\ (Notarized(v) \/ v = ChainRoot) /\ Height(v) >= Height(longest[self])
                /\ longest' = [longest EXCEPT ![self] = v]
                /\ \A w \in V : \neg (w \in Children({v}, chains) /\ w \in votes[self])
                /\ \E w \in (V \ Vertices(chains)) \cup Children({v}, chains):
                     /\ chains' = AddEdge(v, w, chains)
                     /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {w}]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 11:01:40 PST 2021 by nano
\* Created Fri Dec 17 07:53:09 PST 2021 by nano
