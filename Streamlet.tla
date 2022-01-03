----------------------------- MODULE Streamlet -----------------------------

EXTENDS Sequences, FiniteSets, Integers

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   MaxEpoch
    ,   Quorum \* The set of quorums
    ,   Leader(_) \* maps a round to a leader
    
(* 
--algorithm Streamlet {
    variables
        vote = [p \in P |-> {}], \* the vote cast by the processes,
        proposal = [e \in E |-> <<>>];
    define {
        E == 1..MaxEpoch
        Genesis == <<>>
        Epoch(b) ==  \* the epoch of a block
            IF b = <<>> 
            THEN 0 \* note how the root is by convention a block with epoch 0
            ELSE b[Len(b)][1]
        Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1) \* the parent of a block
        Prefix(b1, b2) ==
            /\  Len(b1) <= Len(b2)
            /\  \/  b1 = Genesis
                \/  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
        Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
        Blocks == UNION {vote[p] : p \in P}
        Notarized == {Genesis} \cup \* Genesis is considered notarized by default 
            { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in vote[p] }
        \* Final blocks:
        Final(b) ==  
            /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
            /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : 
            Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
    }
    process (proc \in P)
        variables 
            height = 0, \* height of the longest notarized chain that p voted to extend
            epoch = 1; \* the current epoch of p
    {
l1:     while (epoch \in E) {
            \* if leader, make a proposal:
            if (Leader(epoch) = self) {
                with (parent \in {b \in Notarized : height <= Len(b) /\ Epoch(b) <= epoch}, 
                        tx \in Tx, b = Append(parent, <<epoch, tx>>))
                    proposal[epoch] := b
            };
            \* next, either vote for the leader's proposal or skip:
            either {
                when Len(proposal[epoch]) > height;
                vote[self] := @ \cup {proposal[epoch]};
                height := Len(proposal[epoch])-1
            } or skip; \* skip voting
            \* finally, go to the next epoch
            epoch := epoch + 1;
        }
    }
}
*) 
\* BEGIN TRANSLATION (chksum(pcal) = "ee5319a3" /\ chksum(tla) = "b64df055")
VARIABLES vote, proposal, pc

(* define statement *)
E == 1..MaxEpoch
Genesis == <<>>
Epoch(b) ==
    IF b = <<>>
    THEN 0
    ELSE b[Len(b)][1]
Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1)
Prefix(b1, b2) ==
    /\  Len(b1) <= Len(b2)
    /\  \/  b1 = Genesis
        \/  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
Blocks == UNION {vote[p] : p \in P}
Notarized == {Genesis} \cup
    { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in vote[p] }

Final(b) ==
    /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
    /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
    Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

VARIABLES height, epoch

vars == << vote, proposal, pc, height, epoch >>

ProcSet == (P)

Init == (* Global variables *)
        /\ vote = [p \in P |-> {}]
        /\ proposal = [e \in E |-> <<>>]
        (* Process proc *)
        /\ height = [self \in P |-> 0]
        /\ epoch = [self \in P |-> 1]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF epoch[self] \in E
                  THEN /\ IF Leader(epoch[self]) = self
                             THEN /\ \E parent \in {b \in Notarized : height[self] <= Len(b) /\ Epoch(b) <= epoch[self]}:
                                       \E tx \in Tx:
                                         LET b == Append(parent, <<epoch[self], tx>>) IN
                                           proposal' = [proposal EXCEPT ![epoch[self]] = b]
                             ELSE /\ TRUE
                                  /\ UNCHANGED proposal
                       /\ \/ /\ Len(proposal'[epoch[self]]) > height[self]
                             /\ vote' = [vote EXCEPT ![self] = @ \cup {proposal'[epoch[self]]}]
                             /\ height' = [height EXCEPT ![self] = Len(proposal'[epoch[self]])-1]
                          \/ /\ TRUE
                             /\ UNCHANGED <<vote, height>>
                       /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << vote, proposal, height, epoch >>

proc(self) == l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in P: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Notarized : Final(b2) /\ \neg Compatible(b1, b2))
\* Find a final chain with non-consecutive epoch numbers:
BaitInv3 == \neg (\E b \in Notarized : Final(b) /\ Epoch(b) # Epoch(SubSeq(b,1,1))+Len(b)-1)
=============================================================================
\* Modification History
\* Last modified Sun Jan 02 20:01:23 PST 2022 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
