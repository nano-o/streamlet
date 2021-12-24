----------------------- MODULE SynchronousStreamlet3 -----------------------

(***************************************************************************)
(* Here we specify a simpler version of the crash-fault Streamlet          *)
(* algorithm.                                                              *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets, Sequences

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   Quorum \* The set of quorums
    ,   MaxEpoch       

E == 1..MaxEpoch

Root == <<>> \* the root of the block tree

Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Min(X) == CHOOSE x \in X : \A y \in X : x <= y
Abs(n) == IF n < 0 THEN -n ELSE n
    
Num == \* assigns a process number to each process
    CHOOSE f \in [P -> 1..Cardinality(P)] : 
        \A p1,p2 \in P : p1 # p2 => f[p1] # f[p2]
Proc(n) == \* the inverse of Num
    CHOOSE p \in P : Num[p] = n
    
\* A block is a sequence of pairs where each pair consists of an epoch and a tx set:
IsBlock(b) == 
    /\  DOMAIN b = 1..Len(b) 
    /\  \A i \in DOMAIN b : 
        /\  b[i] = <<b[i][1],b[i][2]>>
        /\  b[i][1] \in E
        /\  b[i][2] \in Tx
Epoch(b) == IF b = Root THEN 0 ELSE b[Len(b)][1]
Payload(b) == b[Len(b)][2]
Parent(b) == SubSeq(b, 1, Len(b)-1)

\* A set of blocks corresponds to a digraph:
DiGraph(Blocks) == LET Edges(b) == 
        CASE 
            Len(b) > 1 -> {<<b[i],b[i+1]>> : i \in 1..(Len(b)-1)} \cup {<<<<0>>, b[1]>>}
        []  Len(b) = 1 -> {<<<<0>>, b[1]>>}
        []  b = <<>> -> {}
    IN  UNION {Edges(b) : b \in {b \in Blocks : b # <<>>}}

Prefix(b1, b2) == Len(b1) <= Len(b2) /\ b1 = SubSeq(b2, 1, Len(b1))
Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> {}], \* the votes cast by the processes
    define {
        Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
        Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
        \* Final blocks:
        Final(b) == 
            /\  b # Root
            /\  \E tx \in Tx :
                    /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
                    /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Main safety property:
        Safety == \A b1,b2 \in Blocks : Final(b1) /\ Final(b2) /\ Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        \* The tip of a notarized chain:
        Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Len(b)
        \* The heights of two competing tips differ at most by 1:
        Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1 
        BaitInv1 == \A b \in Blocks : \neg Final(b)
        BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))
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
                with (b \in Blocks) { \* the notarized block we're going to extend
                    when Len(b) >= height[proc] /\ Notarized(b) /\ Epoch(b) < epoch;
                    with (tx \in Tx) { \* pick a payload
                        votes[proc] := @ \cup {Append(b, <<epoch, tx>>)};
                    };
                    height[proc] := Len(b);
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
\* BEGIN TRANSLATION (chksum(pcal) = "2b0c3c81" /\ chksum(tla) = "5af82c50")
VARIABLES height, votes

(* define statement *)
Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in Blocks : Final(b1) /\ Final(b2) /\ Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)

Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Len(b)

Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1
BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))

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
                        \/ /\ \E b \in Blocks:
                                /\ Len(b) >= height[proc] /\ Notarized(b) /\ Epoch(b) < epoch[self]
                                /\ \E tx \in Tx:
                                     votes' = [votes EXCEPT ![proc] = @ \cup {Append(b, <<epoch[self], tx>>)}]
                                /\ height' = [height EXCEPT ![proc] = Len(b)]
                        \/ /\ TRUE
                           /\ UNCHANGED <<height, votes>>
                   /\ n' = [n EXCEPT ![self] = (n[self]%Cardinality(P)) + 1]
                   /\ IF n'[self] = 1
                         THEN /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]
                         ELSE /\ TRUE
                              /\ epoch' = epoch

Next == (\E self \in {"sched"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 24 15:31:19 PST 2021 by nano
\* Created Fri Dec 24 14:47:10 PST 2021 by nano
