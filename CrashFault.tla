----------------------------- MODULE CrashFault -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, TLC

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
(* The main invariant is that a node has at most one notarized child.  By  *)
(* induction from the root, this means there's a single notarized chain.   *)
(*                                                                         *)
(* TODO: the marking thing does not work...  needs a double-mark of sort.  *)
(***************************************************************************)

ChainRoot == CHOOSE v \in V : TRUE \* we pick an arbitrary root

Abs(n) == IF n < 0 THEN -n ELSE n

(* 
--algorithm Consensus {
    variables
        chains = <<{ChainRoot}, {}>>, \* invariant: will remain a tree
        notarizedHeight = [p \in P |-> 0], \* longest notarized chain seen by p
        votedHeight = [p \in P |-> 0],
        votes = [p \in P |-> {}], \* processes vote for chains vertices
        marked = [p \in P |-> {}], \* a process marks a node if it's one ahead of the max height it ever voted for
    define {
        Notarized(v) == v = ChainRoot \/ \E Q \in Quorum : \A p \in Q : v \in votes[p]  
        Height(v) == Distance({ChainRoot}, v, chains)
        \* The tip of a notarized chain:
        Tip(v) == v \in Vertices(chains) /\ Notarized(v) /\ \A w \in Vertices(chains) : Notarized(w) /\ v # w => \neg Reachable(v, w, chains)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : notarizedHeight[p] <= Height(v)
        \* The heights of two competing tips differ at most by 1:   
        Inv1 == \A v,w \in Vertices(chains) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1
        (*******************************************************************)
        (* By Inv1, we know that if a tip is more than on behind, it can   *)
        (* never be built on anymore.  So we can decide when we detect     *)
        (* that all competing tips must be more than one behind.  This is  *)
        (* when two vertices are notarized in a row.                       *)
        (*******************************************************************)
        \* A notarized vertice is marked when a quorum put a mark on it. When a notarized vertice is marked and its child is notarized and marked, the first can be decided.
        NotarizedMarked(v) == v = ChainRoot \/ \E Q \in Quorum : \A p \in Q : v \in marked[p]
        \* Decided vertices:
        Decided(v) == NotarizedMarked(v) /\ \E w \in Children({v}, chains) : NotarizedMarked(w)
        \* Main safety property:
        Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Reachable(v, w, chains) \/ Reachable(w, v, chains)
    }
    process (proc \in P) {
l1:     \* extend a longer notarized chain with a vote
        while (TRUE)
            with (v \in Vertices(chains)) {
                when Notarized(v) /\ Height(v) >= notarizedHeight[self];
                notarizedHeight[self] := Height(v);
                with (w \in (V \ Vertices(chains)) \cup Children({v}, chains)) { \* pick a fresh vertice or vote for an existing child
                    chains := AddEdge(v, w, chains);
                    votes[self] := votes[self] \cup {w};
                    if (votedHeight[self] < notarizedHeight[self]+1) {
                        marked[self] := marked[self] \cup {w};
                    }; 
                    votedHeight[self] := notarizedHeight[self]+1;
                };
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1f600c9b" /\ chksum(tla) = "2c000c13")
VARIABLES chains, notarizedHeight, votedHeight, votes, marked

(* define statement *)
Notarized(v) == v = ChainRoot \/ \E Q \in Quorum : \A p \in Q : v \in votes[p]
Height(v) == Distance({ChainRoot}, v, chains)

Tip(v) == v \in Vertices(chains) /\ Notarized(v) /\ \A w \in Vertices(chains) : Notarized(w) /\ v # w => \neg Reachable(v, w, chains)

Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : notarizedHeight[p] <= Height(v)

Inv1 == \A v,w \in Vertices(chains) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1







NotarizedMarked(v) == v = ChainRoot \/ \E Q \in Quorum : \A p \in Q : v \in marked[p]

Decided(v) == NotarizedMarked(v) /\ \E w \in Children({v}, chains) : NotarizedMarked(w)

Safety == \A v,w \in Vertices(chains) : Decided(v) /\ Decided(w) => Reachable(v, w, chains) \/ Reachable(w, v, chains)


vars == << chains, notarizedHeight, votedHeight, votes, marked >>

ProcSet == (P)

Init == (* Global variables *)
        /\ chains = <<{ChainRoot}, {}>>
        /\ notarizedHeight = [p \in P |-> 0]
        /\ votedHeight = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        /\ marked = [p \in P |-> {}]

proc(self) == \E v \in Vertices(chains):
                /\ Notarized(v) /\ Height(v) >= notarizedHeight[self]
                /\ notarizedHeight' = [notarizedHeight EXCEPT ![self] = Height(v)]
                /\ \E w \in (V \ Vertices(chains)) \cup Children({v}, chains):
                     /\ chains' = AddEdge(v, w, chains)
                     /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {w}]
                     /\ IF votedHeight[self] < notarizedHeight'[self]+1
                           THEN /\ marked' = [marked EXCEPT ![self] = marked[self] \cup {w}]
                           ELSE /\ TRUE
                                /\ UNCHANGED marked
                     /\ votedHeight' = [votedHeight EXCEPT ![self] = notarizedHeight'[self]+1]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 17:57:23 PST 2021 by nano
\* Created Fri Dec 17 07:53:09 PST 2021 by nano
