----------------------------- MODULE Streamlet -----------------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets

CONSTANTS
        P \* The set of processes
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

Root == CHOOSE v \in V : TRUE

Max(E) == CHOOSE e \in E : \A f \in E : f <= e
Abs(n) == IF n < 0 THEN -n ELSE n


(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> [r \in Round |-> <<>>]], \* the votes cast by the processes
        round = [p \in P |-> 1] \* the current round of a process
    define {
        G == {votes[p][r] : p \in P, r \in Round} \ {<<>>}
        Notarized(r,v) == 
            IF r = 0
            THEN v = Root
            ELSE \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : votes[p][r] = <<w,v>>
        Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)
        \* The tip of a notarized chain:
        Tip(v) == 
            /\  v \in Vertices(G)
            /\  \E r \in Round : Notarized(r,v)
            /\  \A w \in Vertices(G) : \E r \in Round : Notarized(r,w) /\ v # w => \neg Reachable(v, w, G)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(v)
        \* The heights of two competing tips differ at most by 1:   
        Inv1 == \A v,w \in Vertices(G) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1
        \* Decided vertices:
        Decided(v) == \E v1,v3 \in V : \E r \in Round \cup {0}: 
            /\  r+2 <= Max(Round)
            /\  Notarized(r,v1) /\  Notarized(r+1,v) /\  Notarized(r+2,v3)
            /\  <<v1,v>> \in G /\ <<v,v3>> \in G 
        \* Main safety property:
        Safety == \A v,w \in Vertices(G) : Decided(v) /\ Decided(w) => Compatible(w, v, G)
        BaitInv1 == \A v \in V : \neg Decided(v)
    }
    process (proc \in P) {
l1:     while (TRUE) { 
            when round[self] \in Round; \* stop if we ran out of rounds
            when \A p \in P : round[self] = round[p] \/ round[self] = round[p] - 1; \* synchronous round model
            either { \* extend a longer notarized chain with a vote
                with (v \in Vertices(G) \cup {Root}) { \* the notarized vertice we're going to extend
                    when Height(v) >= height[self] /\ \E r \in Round\cup {0} : r < round[self] /\ Notarized(r,v);
                    with (w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G)) \* pick a fresh vertice or vote for an existing child of v
                        \* note that, in the original algorithm, blocks are unique due to hash chaining
                        votes[self][round[self]] := <<v,w>>;
                    height[self] := Height(v);
                }
            } 
            or { \* skip the round
                skip
            };
            round[self] := round[self] + 1 \* go to the next round
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "eec9f378" /\ chksum(tla) = "7c12db08")
VARIABLES height, votes, round

(* define statement *)
G == {votes[p][r] : p \in P, r \in Round} \ {<<>>}
Notarized(r,v) ==
    IF r = 0
    THEN v = Root
    ELSE \E Q \in Quorum, w \in Vertices(G) : \A p \in Q : votes[p][r] = <<w,v>>
Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)

Tip(v) ==
    /\  v \in Vertices(G)
    /\  \E r \in Round : Notarized(r,v)
    /\  \A w \in Vertices(G) : \E r \in Round : Notarized(r,w) /\ v # w => \neg Reachable(v, w, G)

Competing(v) == Tip(v) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(v)

Inv1 == \A v,w \in Vertices(G) : Competing(v) /\ Competing(w) => Abs(Height(v) - Height(w)) <= 1

Decided(v) == \E v1,v3 \in V : \E r \in Round \cup {0}:
    /\  r+2 <= Max(Round)
    /\  Notarized(r,v1) /\  Notarized(r+1,v) /\  Notarized(r+2,v3)
    /\  <<v1,v>> \in G /\ <<v,v3>> \in G

Safety == \A v,w \in Vertices(G) : Decided(v) /\ Decided(w) => Compatible(w, v, G)
BaitInv1 == \A v \in V : \neg Decided(v)


vars == << height, votes, round >>

ProcSet == (P)

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> [r \in Round |-> <<>>]]
        /\ round = [p \in P |-> 1]

proc(self) == /\ round[self] \in Round
              /\ \A p \in P : round[self] = round[p] \/ round[self] = round[p] - 1
              /\ \/ /\ \E v \in Vertices(G) \cup {Root}:
                         /\ Height(v) >= height[self] /\ \E r \in Round\cup {0} : r < round[self] /\ Notarized(r,v)
                         /\ \E w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G):
                              votes' = [votes EXCEPT ![self][round[self]] = <<v,w>>]
                         /\ height' = [height EXCEPT ![self] = Height(v)]
                 \/ /\ TRUE
                    /\ UNCHANGED <<height, votes>>
              /\ round' = [round EXCEPT ![self] = round[self] + 1]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Wed Dec 22 19:56:53 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
