----------------------------- MODULE CrashFault -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
        P \* processors
    ,   V \* values
    ,   Quorum \* Quorums

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

Abs(n) == IF n < 0 THEN -n ELSE n

(* 
--algorithm Consensus {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> {}], \* the votes cast by the processes
    define {
        G == {<<Root,Root>>} \cup UNION {votes[p] : p \in P} 
        Notarized(v) == v = Root \/ \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : <<w,v>> \in votes[p]  
        Height(v) == Distance({Root}, v, G)
        \* The tip of a notarized chain:
        Tip(v) == 
            /\  v \in Vertices(G)
            /\  Notarized(v) 
            /\  \A w \in Vertices(G) : Notarized(w) /\ v # w => \neg Reachable(v, w, G)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(v)
        \* The heights of two competing tips differ at most by 1:   
        Safety == \A v,w \in Vertices(G) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1
        Inv1 == IsDigraph(G)
        Temporal1 == \A v,w \in V\{Root} : v#w => []( 
            Tip(v) /\ Tip(w) /\ Height(v) < Height(w)-1    
                => []( \A u \in V\{Root,v} : \neg Reachable(v,u,G) /\ Notarized(u) ) )
    }
    process (proc \in P) {
l1:     while (TRUE) \* extend a longer notarized chain with a vote
            with (v \in Vertices(G)) { \* the notarized vertice we're going to extend
                when Notarized(v) /\ Height(v) >= height[self];
                height[self] := Height(v);
                \* pick a fresh vertice or vote for an existing child of v:
                with (w \in (V \ Vertices(G)) \cup Children({v}, G)) { 
                    votes[self] := @ \cup {<<v,w>>};
                };
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "574e9dbd" /\ chksum(tla) = "86da9a04")
VARIABLES height, votes

(* define statement *)
G == {<<Root,Root>>} \cup UNION {votes[p] : p \in P}
Notarized(v) == v = Root \/ \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : <<w,v>> \in votes[p]
Height(v) == Distance({Root}, v, G)

Tip(v) ==
    /\  v \in Vertices(G)
    /\  Notarized(v)
    /\  \A w \in Vertices(G) : Notarized(w) /\ v # w => \neg Reachable(v, w, G)

Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(v)

Safety == \A v,w \in Vertices(G) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1
Inv1 == IsDigraph(G)
Temporal1 == \A v,w \in V\{Root} : v#w => [](
    Tip(v) /\ Tip(w) /\ Height(v) <= Height(w)-1
        => []( \A u \in V\{Root,v} : \neg Reachable(v,u,G) /\ Notarized(u) ) )


vars == << height, votes >>

ProcSet == (P)

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]

proc(self) == \E v \in Vertices(G):
                /\ Notarized(v) /\ Height(v) >= height[self]
                /\ height' = [height EXCEPT ![self] = Height(v)]
                /\ \E w \in (V \ Vertices(G)) \cup Children({v}, G):
                     votes' = [votes EXCEPT ![self] = @ \cup {<<v,w>>}]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Dec 19 21:32:25 PST 2021 by nano
\* Created Fri Dec 17 07:53:09 PST 2021 by nano
