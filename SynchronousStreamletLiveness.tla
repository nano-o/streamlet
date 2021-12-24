-------------------- MODULE SynchronousStreamletLiveness --------------------

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
    
Num == \* assigns a process number to each process
    CHOOSE f \in [P -> 1..Cardinality(P)] : 
        \A p1,p2 \in P : p1 # p2 => f[p1] # f[p2]
Proc(n) == \* the inverse of Num
    CHOOSE p \in P : Num[p] = n   

(***************************************************************************)
(* TODO how to check with TLC that steps of different rounds really        *)
(* commute? Do they really commute? It seems that the "pick a fresh        *)
(* vertice" requirement means they don't commute.  However, morally they   *)
(* still do: as values are uninterpreted, it doesn't rally matter which    *)
(* one is picked.                                                          *)
(***************************************************************************)

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> [r \in Round |-> <<>>]], \* the votes cast by the processes
        round = 1, \* the current round
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
        BaitInv2 == \neg (\E v1,v2,v3 \in V : Notarized(1,v1) /\ Notarized(2,v2) /\ v2 \in Children({Root},G) /\ Notarized(3,v3) /\ \neg Compatible(v2, v3, G))
        \* Liveness
        MaxASyncRound == 1 \* the asynchronous rounds
        Liveness == (round = MaxASyncRound+5) => \E v \in Vertices(G) : Decided(v)
    }
    process (scheduler \in {"sched"})
        variables
            n = 1, \* the next process to take a step
            proposal = <<>>; \* in a good round, the proposal
    {
l1:     while (TRUE) {
            when round \in Round; \* stop if we ran out of rounds 
            if (n = 1 /\ round > MaxASyncRound) { \* start of a good round, so pick the proposal
                with (v \in Vertices(G) \cup {Root}) { \* the notarized vertice we're going to extend
                    when round > MaxASyncRound+1 => Tip(v); \* received all messages so we know the tip
                    with (w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G))\* pick a fresh vertice or an existing child of v
                        proposal := <<v,w>>;
                }
            };
            
            with (proc = Proc(n))
            either {
                when round <= MaxASyncRound; \* asynchronous round, even proposal can fail
                with (v \in Vertices(G) \cup {Root}) {\* the notarized vertice we're going to extend
                    \* when Cardinality(Children({v},G)) <= 1; \* limit the fanout to speed up model-checking
                    when Height(v) >= height[proc] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,v);
                        \* TODO problem here, what is the child is from a previous epoch? SOLUTION: add epoch to the value. And maybe we recover commutativity.
                        with (w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G)) \* pick a fresh vertice or an existing child of v. 
                        votes[proc][round] := <<v,w>>;
                    height[proc] := Height(v);
                }
            }   
            or {
                when round > MaxASyncRound; \* synchronous round
                when Height(proposal[1]) >= height[proc] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,proposal[1]);
                votes[proc][round] := proposal;
                height[proc] := Height(proposal[1]);
            } 
            or { \* proc skips the round
                when round = 1; \* only round 1 is asynchronous
                skip
            };
            
            n := (n%Cardinality(P)) + 1;
            if (n = 1) { \* we scheduled all processes
                round := round + 1; \* go to the next round
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cb9d3fa2" /\ chksum(tla) = "8aa03ee3")
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
BaitInv2 == \neg (\E v1,v2,v3 \in V : Notarized(1,v1) /\ Notarized(2,v2) /\ v2 \in Children({Root},G) /\ Notarized(3,v3) /\ \neg Compatible(v2, v3, G))

MaxASyncRound == 1
Liveness == (round = MaxASyncRound+5) => \E v \in Vertices(G) : Decided(v)

VARIABLES n, proposal

vars == << height, votes, round, n, proposal >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> [r \in Round |-> <<>>]]
        /\ round = 1
        (* Process scheduler *)
        /\ n = [self \in {"sched"} |-> 1]
        /\ proposal = [self \in {"sched"} |-> <<>>]

scheduler(self) == /\ round \in Round
                   /\ IF n[self] = 1 /\ round > MaxASyncRound
                         THEN /\ \E v \in Vertices(G) \cup {Root}:
                                   /\ round > MaxASyncRound+1 => Tip(v)
                                   /\ \E w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G):
                                        proposal' = [proposal EXCEPT ![self] = <<v,w>>]
                         ELSE /\ TRUE
                              /\ UNCHANGED proposal
                   /\ LET proc == Proc(n[self]) IN
                        \/ /\ round <= MaxASyncRound
                           /\ \E v \in Vertices(G) \cup {Root}:
                                /\ Height(v) >= height[proc] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,v)
                                /\ \E w \in (V \ (Vertices(G)\cup {Root})) \cup Children({v}, G):
                                     votes' = [votes EXCEPT ![proc][round] = <<v,w>>]
                                /\ height' = [height EXCEPT ![proc] = Height(v)]
                        \/ /\ round > MaxASyncRound
                           /\ Height(proposal'[self][1]) >= height[proc] /\ \E r \in Round\cup {0} : r < round /\ Notarized(r,proposal'[self][1])
                           /\ votes' = [votes EXCEPT ![proc][round] = proposal'[self]]
                           /\ height' = [height EXCEPT ![proc] = Height(proposal'[self][1])]
                        \/ /\ round = 1
                           /\ TRUE
                           /\ UNCHANGED <<height, votes>>
                   /\ n' = [n EXCEPT ![self] = (n[self]%Cardinality(P)) + 1]
                   /\ IF n'[self] = 1
                         THEN /\ round' = round + 1
                         ELSE /\ TRUE
                              /\ round' = round

Next == (\E self \in {"sched"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Dec 23 17:50:32 PST 2021 by nano
\* Created Thu Dec 23 16:22:06 PST 2021 by nano
