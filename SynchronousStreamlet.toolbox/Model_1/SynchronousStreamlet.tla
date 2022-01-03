------------------------ MODULE SynchronousStreamlet ------------------------

EXTENDS Sequences, FiniteSets, Integers

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   MaxEpoch
    ,   Quorum \* The set of quorums
    ,   GSE
    
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
        epoch = 1, \* the current epoch
        n = 1, \* the next process to take a step
        proposal = <<>>; \* the proposal of the leader for the current epoch
    define {
        E == 1..MaxEpoch
        Max(X) == CHOOSE x \in X : \A y \in X : y <= x
        Root == <<>>
        Epoch(b) ==  \* the epoch of a block
            IF b = <<>> 
            THEN 0 \* note how the root is by convention a block with epoch 0
            ELSE b[Len(b)][1]
        Parent(b) == IF Len(b) = 1 THEN Root ELSE SubSeq(b, 1, Len(b)-1) \* the parent of a block
        Prefix(b1, b2) ==
            /\  Len(b1) <= Len(b2)
            /\  \/  b1 = Root
                \/  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
        Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
        Blocks == UNION {votes[p] : p \in P}
        Notarized == {Root} \cup \* Root is considered notarized by default 
            { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in votes[p] }
        \* Final blocks:
        Final(b) ==  
            /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
            /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : 
            Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        \* Liveness property; it takes at most 4 epochs to finalize a new block: 
        Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1
        \* Invariants:
        Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
        Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ b2 \in Notarized /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
        Inv3 == \A b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
        Inv4 == \A b \in Blocks : b \in Notarized /\ (\E tx \in Tx : Append(b, <<Epoch(b)+1, tx>>)) \in Notarized 
                    => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
    }
    process (scheduler \in {"sched"})
    {
l1:     while (epoch \in E) {
           if (n = 1) { \* we're starting the epoch, so pick a proposal
                with (b \in Notarized) {
                    \* after the first synchronous epoch, the leader is able to pick a notarized block with the highest height:
                    when epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(b);
                    with (tx \in Tx)
                        proposal := Append(b, <<epoch,tx>>)
                }
            };
            with (proc = Proc(n)) \* process number n takes a step
            \* if possible, vote for the leader's proposal:
            either {
                with (maxLen \in height[proc]..Max({Len(b) : b \in Notarized})) { \* the max notarized length known to proc
                    when epoch > GSE => \A b2 \in Notarized : Len(b2) <= maxLen;
                    if (maxLen <= Len(proposal)-1) { \* vote if possible
                        votes[proc] := @ \cup {proposal};
                        height[proc] := Len(proposal)-1;
                    }
                    else 
                        height[proc] := maxLen;
                }
            }
            or {
                when epoch < GSE; \* Before GSE, we may miss the leader's proposal
                skip
            };
            \* now schedule the next process:
            if (n = Cardinality(P)) {
                n := 1;
                epoch := epoch+1
            }
            else
                n := n+1
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "690fe5e5" /\ chksum(tla) = "6d41a688")
VARIABLES height, votes, epoch, n, proposal, pc

(* define statement *)
E == 1..MaxEpoch
Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Root == <<>>
Epoch(b) ==
    IF b = <<>>
    THEN 0
    ELSE b[Len(b)][1]
Parent(b) == IF Len(b) = 1 THEN Root ELSE SubSeq(b, 1, Len(b)-1)
Prefix(b1, b2) ==
    /\  Len(b1) <= Len(b2)
    /\  \/  b1 = Root
        \/  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
Blocks == UNION {votes[p] : p \in P}
Notarized == {Root} \cup
    { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in votes[p] }

Final(b) ==
    /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
    /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
    Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1

Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ b2 \in Notarized /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
Inv3 == \A b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
Inv4 == \A b \in Blocks : b \in Notarized /\ (\E tx \in Tx : Append(b, <<Epoch(b)+1, tx>>)) \in Notarized
            => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)


vars == << height, votes, epoch, n, proposal, pc >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        /\ epoch = 1
        /\ n = 1
        /\ proposal = <<>>
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF epoch \in E
                  THEN /\ IF n = 1
                             THEN /\ \E b \in Notarized:
                                       /\ epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(b)
                                       /\ \E tx \in Tx:
                                            proposal' = Append(b, <<epoch,tx>>)
                             ELSE /\ TRUE
                                  /\ UNCHANGED proposal
                       /\ LET proc == Proc(n) IN
                            \/ /\ \E maxLen \in height[proc]..Max({Len(b) : b \in Notarized}):
                                    /\ epoch > GSE => \A b2 \in Notarized : Len(b2) <= maxLen
                                    /\ IF maxLen <= Len(proposal')-1
                                          THEN /\ votes' = [votes EXCEPT ![proc] = @ \cup {proposal'}]
                                               /\ height' = [height EXCEPT ![proc] = Len(proposal')-1]
                                          ELSE /\ height' = [height EXCEPT ![proc] = maxLen]
                                               /\ votes' = votes
                            \/ /\ epoch < GSE
                               /\ TRUE
                               /\ UNCHANGED <<height, votes>>
                       /\ IF n = Cardinality(P)
                             THEN /\ n' = 1
                                  /\ epoch' = epoch+1
                             ELSE /\ n' = n+1
                                  /\ epoch' = epoch
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << height, votes, epoch, n, proposal >>

scheduler(self) == l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"sched"}: scheduler(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* The tip of a notarized chain:
Tip(b) == b \in Notarized /\ \A b2 \in Blocks: b # b2 /\ Prefix(b,b2) => \neg b2 \in Notarized
BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Final(b2) /\ \neg Compatible(b1, b2))
BaitInv3 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ Len(b1) = 2 /\ proposal = b2 /\ \neg Compatible(b1,b2))
BaitInv4 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Len(b1) = 2 /\ Len(b2) = 2 /\ \neg Compatible(b1,b2) /\ \neg Compatible(SubSeq(b1,1,1),SubSeq(b2,1,1)))
BaitInv5 == \neg (
    (\E b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Len(b1) = 2 /\ Len(b2) = 2 /\ \neg Compatible(b1,b2) /\ \neg Compatible(SubSeq(b1,1,1),SubSeq(b2,1,1)))
    /\ epoch = 6 /\ \A b \in Blocks : b \in Notarized => Epoch(b) # 5 )
=============================================================================
\* Modification History
\* Last modified Sun Jan 02 14:49:47 PST 2022 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
