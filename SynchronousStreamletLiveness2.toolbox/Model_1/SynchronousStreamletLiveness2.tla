------------------- MODULE SynchronousStreamletLiveness2 -------------------

EXTENDS Integers, TLC, FiniteSets, Sequences

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   Quorum \* The set of quorums
    ,   MaxEpoch
    ,   GSE \* The first synchronous epoch; all epochs are synchronous after it.
    \* TODO change to FirstSyncEpoch to make counting easier

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

Prefix(b1, b2) == Len(b1) < Len(b2) /\ b1 = SubSeq(b2, 1, Len(b1)) \* strict prefix
Compatible(b1, b2) == b1 = b2 \/ Prefix(b1, b2) \/ Prefix(b2, b1)

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> {}], \* the votes cast by the processes
        epoch = 1, \* the current epoch
        n = 1, \* the next process to take a step
        proposal = <<>>; \* in a synchronous epoch, the proposal of the leader
    define {
        Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
        BlocksBefore(e) == {b \in Blocks : Epoch(b) < e}
        Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
        \* Final blocks:
        Final(b) == 
            /\  b # Root
            /\  \E tx \in Tx :
                    /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
                    /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Main safety property:
        \* Safety == \A b1,b2 \in Blocks : Final(b1) /\ Final(b2) /\ Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        \* The tip of a notarized chain:
        Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)
        TipBefore(e, b) == Notarized(b) /\ \A b2 \in BlocksBefore(e) : Prefix(b,b2) => \neg Notarized(b2)
        \* A tip is still competing if a quorum has a lower or equal notarized height:
        Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Len(b)
        \* The heights of two competing tips differ at most by 1:
        Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1 
        BaitInv1 == \A b \in Blocks : \neg Final(b)
        BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))
        \* Liveness property; it takes at most 4 epochs to finalize a new block: 
        Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1
    }
    macro setProposal() {
        with (b \in Blocks) { \* first pick a block to extend
            when Notarized(b);
            \* after the first synchronous epoch, the leader picks one of the longest notarized blocks.
            \* Otherwise, the leader can pick any notarized node.
            \* when epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Len(b2) <= Len(b);
            when epoch >= GSE+1 => Tip(b) /\ \A b2 \in Blocks : Notarized(b2) => Epoch(b2) <= Epoch(b);
            with (tx \in Tx)
                proposal := Append(b, <<epoch,tx>>)
        }
    }
    macro setupNextStep() {
        if (n = Cardinality(P)) {
            n := 1;
            epoch := epoch+1
        }
        else {
            n := n+1
        }
    }
    process (scheduler \in {"sched"})
    {
l1:     while (TRUE) {
            when epoch \in E; \* stop if we ran out of epochs
            if (n = 1 /\ epoch >= GSE) { \* we're starting a synchronous epoch; pick a proposal
                setProposal()
            };
            with (proc = Proc(n)) \* process number n takes a step
            either {
                \* before GSE:
                when epoch < GSE;
                either { \* vote
                    with (b \in Blocks) { \* the notarized block we're going to extend
                        when Len(b) >= height[proc] /\ Notarized(b);
                        with (tx \in Tx, newB = Append(b, <<epoch, tx>>))\* pick a payload to form the new block
                            votes[proc] := @ \cup {newB};
                        height[proc] := Len(b);
                    }
                }
                or { \* skip this epoch
                    skip
                }
            } 
            or {
                \* starting at GSE:
                when epoch >= GSE;
                \* vote for the proposal if possible
                if (height[proc] <= Len(proposal)-1) { \* Note that Notarized(parent) is always true 
                    votes[proc] := @ \cup {proposal};
                    height[proc] := Len(proposal)-1;
                }
                else
                    skip;
            };
            setupNextStep()
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7a280470" /\ chksum(tla) = "cd3aa591")
VARIABLES height, votes, epoch, n, proposal

(* define statement *)
Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
BlocksBefore(e) == {b \in Blocks : Epoch(b) < e}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1


Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)
TipBefore(e, b) == Notarized(b) /\ \A b2 \in BlocksBefore(e) : Prefix(b,b2) => \neg Notarized(b2)

Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : height[p] <= Len(b)

Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1
BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))

Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1


vars == << height, votes, epoch, n, proposal >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        /\ epoch = 1
        /\ n = 1
        /\ proposal = <<>>

scheduler(self) == /\ epoch \in E
                   /\ IF n = 1 /\ epoch >= GSE
                         THEN /\ \E b \in Blocks:
                                   /\ Notarized(b)
                                   /\ epoch >= GSE+1 => Tip(b) /\ \A b2 \in Blocks : Notarized(b2) => Epoch(b2) <= Epoch(b)
                                   /\ \E tx \in Tx:
                                        proposal' = Append(b, <<epoch,tx>>)
                         ELSE /\ TRUE
                              /\ UNCHANGED proposal
                   /\ LET proc == Proc(n) IN
                        \/ /\ epoch < GSE
                           /\ \/ /\ \E b \in Blocks:
                                      /\ Len(b) >= height[proc] /\ Notarized(b)
                                      /\ \E tx \in Tx:
                                           LET newB == Append(b, <<epoch, tx>>) IN
                                             votes' = [votes EXCEPT ![proc] = @ \cup {newB}]
                                      /\ height' = [height EXCEPT ![proc] = Len(b)]
                              \/ /\ TRUE
                                 /\ UNCHANGED <<height, votes>>
                        \/ /\ epoch >= GSE
                           /\ IF height[proc] <= Len(proposal')-1
                                 THEN /\ votes' = [votes EXCEPT ![proc] = @ \cup {proposal'}]
                                      /\ height' = [height EXCEPT ![proc] = Len(proposal')-1]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << height, votes >>
                   /\ IF n = Cardinality(P)
                         THEN /\ n' = 1
                              /\ epoch' = epoch+1
                         ELSE /\ n' = n+1
                              /\ epoch' = epoch

Next == (\E self \in {"sched"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


BaitInv3 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Len(b1) = 2 /\ proposal = b2 /\ \neg Compatible(b1,b2))
BaitInv4 == epoch # 6
(*
State1 ==
/\  epoch = 3
/\  height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 1)
/\  n = 2
/\  proposal = <<<<3, Tx1>>>>
/\  votes = ( p1 :> {<<<<1, Tx1>>>>, <<<<2, Tx1>>>>, <<<<3, Tx1>>>>} @@
  p2 :> {<<<<1, Tx1>>>>, <<<<1, Tx1>>, <<2, Tx1>>>>} @@
  p3 :> {<<<<1, Tx1>>>>, <<<<1, Tx1>>, <<2, Tx1>>>>} )
*)
=============================================================================
\* Modification History
\* Last modified Mon Dec 27 13:17:24 PST 2021 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
