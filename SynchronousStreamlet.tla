------------------------ MODULE SynchronousStreamlet ------------------------

EXTENDS Sequences, FiniteSets, Integers

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   MaxEpoch
    ,   Quorum \* The set of quorums
    ,   GSE
    ,   Leader(_)
    
Num == \* assigns a process number to each process
    CHOOSE f \in [P -> 1..Cardinality(P)] : 
        \A p1,p2 \in P : p1 # p2 => f[p1] # f[p2]
Proc(n) == \* the inverse of Num
    CHOOSE p \in P : Num[p] = n

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized p voted to extend
        votes = [p \in P |-> {}], \* the votes cast by the processes
        epoch = 1, \* the current epoch
        scheduled = {}, \* the processes that have been scheduled already in the current epoch
        proposal = <<>>; \* the proposal of the leader for the current epoch
    define {
        E == 1..MaxEpoch
        Max(X) == CHOOSE x \in X : \A y \in X : y <= x
        Genesis == <<>>
        Epoch(b) ==  \* the epoch of a block
            IF b = <<>> 
            THEN 0 \* note how the root is by convention a block with epoch 0
            ELSE b[Len(b)][1]
        Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1) \* the parent of a block
        Blocks == UNION {votes[p] : p \in P}
        Notarized == {Genesis} \cup \* Genesis is considered notarized by default 
            { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in votes[p] }
        \* Final blocks:
        Final(b) ==  
            /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
            /\  Epoch(Parent(b)) = Epoch(b)-1
        NextProc == 
            IF scheduled = {}
            THEN CHOOSE p \in P : Leader(epoch) = p
            ELSE CHOOSE p \in P : \neg p \in scheduled
        \* Safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : 
            Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        \* Liveness property; it takes at most 4 epochs to finalize a new block: 
        Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1
    }
    process (scheduler \in {"sched"})
    {
l1:     while (epoch \in E) {
            with (proc = NextProc) {
                \* if proc is leader, make a proposal:
                if (Leader(epoch) = proc)
                    with (parent \in {b \in Notarized : height[proc] <= Len(b) /\ Epoch(b) <= epoch}, 
                            tx \in Tx, b = Append(parent, <<epoch, tx>>)) {
                        \* after the first synchronous epoch, the leader is able to pick a notarized block with the highest height:
                        when epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(parent);
                        proposal := b
                    };
                \* next, if possible, vote for the leader's proposal:
                either if (height[proc] <= Len(proposal)-1) {
                    votes[proc] := @ \cup {proposal};
                    height[proc] := Len(proposal)-1
                }
                or {
                    when epoch < GSE; \* Before GSE, we may miss the leader's proposal
                    skip
                };
                \* go to the next epoch if all processes have been scheduled:
                if (scheduled \cup {proc} = P) {
                    scheduled := {};
                    epoch := epoch+1
                }
                else 
                    scheduled := scheduled \cup {proc}
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "55674737" /\ chksum(tla) = "e5a67733")
VARIABLES height, votes, epoch, scheduled, proposal, pc

(* define statement *)
E == 1..MaxEpoch
Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Genesis == <<>>
Epoch(b) ==
    IF b = <<>>
    THEN 0
    ELSE b[Len(b)][1]
Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1)
Blocks == UNION {votes[p] : p \in P}
Notarized == {Genesis} \cup
    { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in votes[p] }

Final(b) ==
    /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
    /\  Epoch(Parent(b)) = Epoch(b)-1
NextProc ==
    IF scheduled = {}
    THEN CHOOSE p \in P : Leader(epoch) = p
    ELSE CHOOSE p \in P : \neg p \in scheduled

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
    Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1


vars == << height, votes, epoch, scheduled, proposal, pc >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        /\ epoch = 1
        /\ scheduled = {}
        /\ proposal = <<>>
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF epoch \in E
                  THEN /\ LET proc == NextProc IN
                            /\ IF Leader(epoch) = proc
                                  THEN /\ \E parent \in {b \in Notarized : height[proc] <= Len(b) /\ Epoch(b) <= epoch}:
                                            \E tx \in Tx:
                                              LET b == Append(parent, <<epoch, tx>>) IN
                                                /\ epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(parent)
                                                /\ proposal' = b
                                  ELSE /\ TRUE
                                       /\ UNCHANGED proposal
                            /\ \/ /\ IF height[proc] <= Len(proposal')-1
                                        THEN /\ votes' = [votes EXCEPT ![proc] = @ \cup {proposal'}]
                                             /\ height' = [height EXCEPT ![proc] = Len(proposal')-1]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << height, votes >>
                               \/ /\ epoch < GSE
                                  /\ TRUE
                                  /\ UNCHANGED <<height, votes>>
                            /\ IF scheduled \cup {proc} = P
                                  THEN /\ scheduled' = {}
                                       /\ epoch' = epoch+1
                                  ELSE /\ scheduled' = (scheduled \cup {proc})
                                       /\ epoch' = epoch
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << height, votes, epoch, scheduled, 
                                       proposal >>

scheduler(self) == l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"sched"}: scheduler(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Prefix(b1, b2) ==
    /\  Len(b1) <= Len(b2)
    /\  \/  b1 = Genesis
        \/  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)

\* Invariants:
Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ b2 \in Notarized /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
Inv3 == \A b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
Inv4 == \A b \in Blocks : b \in Notarized /\ (\E tx \in Tx : Append(b, <<Epoch(b)+1, tx>>)) \in Notarized 
            => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
                    
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
\* Last modified Sun Jan 02 20:33:58 PST 2022 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
