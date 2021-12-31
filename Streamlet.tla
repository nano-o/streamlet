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
        votes = [p \in P |-> {}], \* the votes cast by the processes,
        proposal = [e \in E |-> <<>>];
    define {
        E == 1..MaxEpoch
        Root == <<>>
        Epoch(b) ==  \* the epoch of a block
            IF b = <<>> 
            THEN 0 \* note how the root is by convention a block with epoch 0
            ELSE b[Len(b)][1]
        Parent(b) == SubSeq(b, 1, Len(b)-1) \* the parent of a block
        Prefix(b1, b2) == Len(b1) < Len(b2) /\ b1 = SubSeq(b2, 1, Len(b1)) \* strict prefix
        Compatible(b1, b2) == b1 = b2 \/ Prefix(b1, b2) \/ Prefix(b2, b1)
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
    }
    process (proc \in P)
        variables 
            height = 0, \* height of the longest notarized chain seen by p
            epoch = 1; \* the current epoch of p
    {
l1:     while (epoch \in E) {
            with (newB \in Notarized) {
                \* learn of new notarized blocks and record the height of the highest:   
                when newB \in Notarized /\ Len(newB) >= height /\ Epoch(newB) < epoch;
                height := Len(newB);
            };
            \* leader makes a proposal:
            either {
                when (proposal[epoch] = <<>>);
                with (parent \in {b \in Notarized : Len(b) <= height}, 
                        tx \in Tx, b = Append(parent, <<epoch, tx>>))
                    proposal[epoch] := b
            } or skip;
            \* either vote for the leader's proposal or skip:
            either {
                when Len(proposal[epoch]) = height+1;
                votes[self] := @ \cup {proposal[epoch]}
            } or skip; \* skip voting
            epoch := epoch + 1;
        }
    }
}
*) 
\* BEGIN TRANSLATION (chksum(pcal) = "4609b012" /\ chksum(tla) = "8fe89bf2")
VARIABLES votes, proposal, pc

(* define statement *)
E == 1..MaxEpoch
Root == <<>>
Epoch(b) ==
    IF b = <<>>
    THEN 0
    ELSE b[Len(b)][1]
Parent(b) == SubSeq(b, 1, Len(b)-1)
Prefix(b1, b2) == Len(b1) < Len(b2) /\ b1 = SubSeq(b2, 1, Len(b1))
Compatible(b1, b2) == b1 = b2 \/ Prefix(b1, b2) \/ Prefix(b2, b1)
Blocks == UNION {votes[p] : p \in P}
Notarized == {Root} \cup
    { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in votes[p] }

Final(b) ==
    /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
    /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
    Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

VARIABLES height, epoch

vars == << votes, proposal, pc, height, epoch >>

ProcSet == (P)

Init == (* Global variables *)
        /\ votes = [p \in P |-> {}]
        /\ proposal = [e \in E |-> <<>>]
        (* Process proc *)
        /\ height = [self \in P |-> 0]
        /\ epoch = [self \in P |-> 1]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF epoch[self] \in E
                  THEN /\ \E newB \in Notarized:
                            /\ newB \in Notarized /\ Len(newB) >= height[self] /\ Epoch(newB) < epoch[self]
                            /\ height' = [height EXCEPT ![self] = Len(newB)]
                       /\ \/ /\ (proposal[epoch[self]] = <<>>)
                             /\ \E parent \in {b \in Notarized : Len(b) <= height'[self]}:
                                  \E tx \in Tx:
                                    LET b == Append(parent, <<epoch[self], tx>>) IN
                                      proposal' = [proposal EXCEPT ![epoch[self]] = b]
                          \/ /\ TRUE
                             /\ UNCHANGED proposal
                       /\ \/ /\ Len(proposal'[epoch[self]]) = height'[self]+1
                             /\ votes' = [votes EXCEPT ![self] = @ \cup {proposal'[epoch[self]]}]
                          \/ /\ TRUE
                             /\ votes' = votes
                       /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << votes, proposal, height, epoch >>

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
=============================================================================
\* Modification History
\* Last modified Thu Dec 30 19:43:56 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
