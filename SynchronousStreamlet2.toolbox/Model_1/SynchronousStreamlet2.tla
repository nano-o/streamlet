----------------------- MODULE SynchronousStreamlet2 -----------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets

CONSTANTS
        P \* The set of processes
    ,   Tx \* The set of values
    ,   Quorum \* The set of quorums
    ,   E \* The set of rounds. Should be of the form 1..N       

(***************************************************************************)
(* First we need a few notions about directed graphs.  A directed graph is *)
(* a set of edges.                                                         *)
(***************************************************************************)

IsDigraph(G) == \A e \in G : e = <<e[1], e[2]>>  

Vertices(G) == {e[1] : e \in G} \union {e[2] : e \in G}
    
Children(W, G) == UNION {{w \in Vertices(G) : <<v,w>> \in G} : v \in W} 
            
RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, G) == \* v2 is reachable from v1 
\* CAUTION: does not terminate if there is a cycle reachable from v1
    \/  v1 = v2
    \/  v1 # v2 /\ <<v1,v2>> \in G
    \/  \E v3 \in Children({v1}, G) : v1 # v3 /\ Reachable(v3, v2, G)
        
Compatible(v, w, G) == Reachable(v, w, G) \/ Reachable(w, v, G)

RECURSIVE Distance(_,_,_)
Distance(W, v, G) == \* W is a set of vertices
    CASE
        v \in W -> 0
    []  v \in Children(W,G) -> 1
    []  OTHER -> 1 + Distance(Children(W,G)\W, v, G)

Root == <<0, CHOOSE tx \in Tx : TRUE>>

Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Abs(n) == IF n < 0 THEN -n ELSE n
    
Num == \* assigns a process number to each process
    CHOOSE f \in [P -> 1..Cardinality(P)] : 
        \A p1,p2 \in P : p1 # p2 => f[p1] # f[p2]
Proc(n) == \* the inverse of Num
    CHOOSE p \in P : Num[p] = n   

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> {}], \* the votes cast by the processes
    define {
        \* A block consists of a parent block (identified by its epoch and payload), an epoch, and a payload:
        IsBlock(b) == 
            LET parent == b[1]
                epoch == b[2][1]
                payload == b[2][2]
                parentEpoch == parent[1]
                parentPayload == parent[2]
            IN b = <<parent, <<epoch, payload>>>> /\ parent = <<parentEpoch, parentPayload>>
        Epoch(b) == IF b = Root THEN 0 ELSE b[2][1] \* the epoch of a block
        \* the digraph formed by all the blocks ever voted:
        G == UNION {votes[p] : p \in P}
        Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
        Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)
        \* Final blocks:
        Final(b1) == \E b0,b2 \in Tx :
            /\  Notarized(b0) /\  Notarized(b1) /\  Notarized(b2)
            /\  <<b0,b1>> \in G /\ <<b1,b2>> \in G
            /\  Epoch(b1) = Epoch(b0)+1 /\ Epoch(b2) = Epoch(b1)+1
        \* Main safety property:
        Safety == \A b1,b2 \in Vertices(G) : Final(b1) /\ Final(b2) => Compatible(b1, b2, G)
        \* The tip of a notarized chain:
        Tip(b) ==
            /\  Notarized(b)
            /\  \A c \in Vertices(G) : Notarized(c) /\ b # c => \neg Reachable(c, b, G)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(b)
        \* The heights of two competing tips differ at most by 1:
        Inv1 == \A b1,b2 \in Vertices(G) : Competing(b2) /\ Competing(b2) => Abs(Height(b1) - Height(b2)) <= 1 
        BaitInv1 == \A b \in Vertices(G) : \neg Final(b)
        BaitInv2 == \neg (\E b1,b2 \in Vertices(G) : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2, G))
    }
    process (scheduler \in {"sched"})
        variables
            epoch = 1, \* the current epoch
            n = 1; \* the next process to take a step
    {
l1:     while (TRUE) {
            when epoch \in E; \* stop if we ran out of epochs
            with (proc = Proc(n))
            either { \* proc extends a longer notarized chain with a vote
                with (b \in G \cup {<<Root,Root>>}) { \* the notarized block we're going to extend
                    \* when Height(b) >= height[proc] /\ Notarized(b) /\ Epoch(b) < epoch;
                    when Cardinality(Children({b[2]},G)) <= 1; \* limit the fanout to speed up model-checking
                    with (tx \in Tx) { \* pick a payload
                        votes[proc] := @ \cup {<<b[2],<<epoch,tx>>>>};
                    };
                    \* height[proc] := Height(b);
                }
            } 
            or { \* proc skips the epoch
                skip
            };
            n := (n%Cardinality(P)) + 1;
            if (n = 1) { \* we scheduled all processes
                epoch := epoch + 1; \* go to the next epoch
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e100ac51" /\ chksum(tla) = "4e0cf28d")
VARIABLES height, votes

(* define statement *)
IsBlock(b) ==
    LET parent == b[1]
        epoch == b[2][1]
        payload == b[2][2]
        parentEpoch == parent[1]
        parentPayload == parent[2]
    IN b = <<parent, <<epoch, payload>>>> /\ parent = <<parentEpoch, parentPayload>>
Epoch(b) == IF b = Root THEN 0 ELSE b[2][1]

G == UNION {votes[p] : p \in P}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
Height(v) == IF v = Root THEN 0 ELSE Distance({Root}, v, G)

Final(b1) == \E b0,b2 \in Tx :
    /\  Notarized(b0) /\  Notarized(b1) /\  Notarized(b2)
    /\  <<b0,b1>> \in G /\ <<b1,b2>> \in G
    /\  Epoch(b1) = Epoch(b0)+1 /\ Epoch(b2) = Epoch(b1)+1

Safety == \A b1,b2 \in Vertices(G) : Final(b1) /\ Final(b2) => Compatible(b1, b2, G)

Tip(b) ==
    /\  Notarized(b)
    /\  \A c \in Vertices(G) : Notarized(c) /\ b # c => \neg Reachable(c, b, G)

Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Height(b)

Inv1 == \A b1,b2 \in Vertices(G) : Competing(b2) /\ Competing(b2) => Abs(Height(b1) - Height(b2)) <= 1
BaitInv1 == \A b \in Vertices(G) : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Vertices(G) : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2, G))

VARIABLES epoch, n

vars == << height, votes, epoch, n >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        (* Process scheduler *)
        /\ epoch = [self \in {"sched"} |-> 1]
        /\ n = [self \in {"sched"} |-> 1]

scheduler(self) == /\ epoch[self] \in E
                   /\ LET proc == Proc(n[self]) IN
                        \/ /\ \E b \in G \cup {<<Root,Root>>}:
                                /\ Cardinality(Children({b[2]},G)) <= 1
                                /\ \E tx \in Tx:
                                     votes' = [votes EXCEPT ![proc] = @ \cup {<<b[2],<<epoch[self],tx>>>>}]
                        \/ /\ TRUE
                           /\ votes' = votes
                   /\ n' = [n EXCEPT ![self] = (n[self]%Cardinality(P)) + 1]
                   /\ IF n'[self] = 1
                         THEN /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]
                         ELSE /\ TRUE
                              /\ epoch' = epoch
                   /\ UNCHANGED height

Next == (\E self \in {"sched"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Thu Dec 23 16:18:52 PST 2021 by nano
\* Created Thu Dec 23 15:19:12 PST 2021 by nano
