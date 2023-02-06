----------------------------- MODULE Streamlet -----------------------------

(***************************************************************************)
(* This is a specification of a crash-stop version of the Streamlet        *)
(* consensus algorithm.  See the following blog post for more details:     *)
(* https://www.losa.fr/blog/streamlet-in-tla+                              *)
(***************************************************************************)


EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS
        P \* The set of processes
    ,   TxSet \* Transtaction sets (the payload in a block)
    ,   Quorum \* The set of quorums
    ,   Leader(_) \* maps a round to a leader

(*
--algorithm Streamlet {
    variables
        vote = [p \in P |-> {}], \* the vote cast by the processes
        proposal = [e \in Nat |-> <<>>]; \* the proposal for each epoch
    define {
        (*******************************************************************)
        (* The genesis block is the empty sequence:                        *)
        (*******************************************************************)
        Genesis == <<>>
        (*******************************************************************)
        (* We model blocks as sequences of pairs, where each pair consists *)
        (* of a transaction set and an epoch.  The epoch of a block is the *)
        (* epoch element of the last pair in the sequence.                 *)
        (*******************************************************************)
        Epoch(b) ==
            IF b = <<>>
            THEN 0 \* the genesis block has epoch 0 by convention
            ELSE b[Len(b)][1]
        (*******************************************************************)
        (* The parent of a block b of length l is just the prefix of b of  *)
        (* length l-1:                                                     *)
        (*******************************************************************)
        Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1)
        Prefix(b1, b2) ==
            /\  Len(b1) <= Len(b2)
            /\  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
        (*******************************************************************)
        (* Two blocks b1 and b2 are compatible when one is a prefix of the *)
        (* other:                                                          *)
        (*******************************************************************)
        Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
        \* The set of blocks voted for by at least one process:
        Blocks == UNION {vote[p] : p \in P}
        (*******************************************************************)
        (* A block is notarized when a quorum voted for it:                *)
        (*******************************************************************)
        Notarized == {Genesis} \cup \* Genesis is considered notarized by default
            { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in vote[p] }
        (*******************************************************************)
        (* A block b with epoch e is final when it has a sucessor          *)
        (* notarized at epoch e+1 and a parent with epoch e-1:             *)
        (*******************************************************************)
        Final(b) ==
            /\  \E txs \in TxSet : Append(b, <<Epoch(b)+1,txs>>) \in Notarized
            /\  Epoch(Parent(b)) = Epoch(b)-1
        FinalBlocks == {b \in Blocks : Final(b)}
        (*******************************************************************)
        (* The safety property: every two final blocks are compatible,     *)
        (* i.e.  final blocks form a chain.                                *)
        (*******************************************************************)
        Safety == \A b1,b2 \in FinalBlocks : Compatible(b1,b2)
    }
    process (proc \in P)
        variables
            height = 0, \* height of the longest notarized chain that the process voted to extend
            epoch = 1; \* the current epoch of the process
    {
l1:     while (TRUE) {
            (***************************************************************)
            (* If leader, propose a block extending one of the longest     *)
            (* notarized chains that the process has seen:                 *)
            (***************************************************************) 
            if (Leader(epoch) = self) {
                \* we non-deterministically pick a notarized block (longer than height) to extend
                \* this abstracts over what the leader has seen:
                with (parent \in {b \in Notarized : height <= Len(b)})
                with (txs \in TxSet)
                with(b = Append(parent, <<epoch, txs>>))
                    proposal[epoch] := b
            };
            (***************************************************************)
            (* Next, either vote for the leader's proposal or do nothing   *)
            (* (e.g.  because the leader's proposal was not received):     *)
            (***************************************************************)
            either {
                when Len(proposal[epoch]) > height;
                vote[self] := @ \cup {proposal[epoch]};
                height := Len(proposal[epoch])-1
            } 
            or skip;
            \* finally, go to the next epoch
            epoch := epoch + 1;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cd49cb42" /\ chksum(tla) = "64fd1d5c")
VARIABLES vote, proposal

(* define statement *)
Genesis == <<>>





Epoch(b) ==
    IF b = <<>>
    THEN 0
    ELSE b[Len(b)][1]




Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1)
Prefix(b1, b2) ==
    /\  Len(b1) <= Len(b2)
    /\  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))




Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)

Blocks == UNION {vote[p] : p \in P}



Notarized == {Genesis} \cup
    { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in vote[p] }




Final(b) ==
    /\  \E txs \in TxSet : Append(b, <<Epoch(b)+1,txs>>) \in Notarized
    /\  Epoch(Parent(b)) = Epoch(b)-1
FinalBlocks == {b \in Blocks : Final(b)}




Safety == \A b1,b2 \in FinalBlocks : Compatible(b1,b2)

VARIABLES height, epoch

vars == << vote, proposal, height, epoch >>

ProcSet == (P)

Init == (* Global variables *)
        /\ vote = [p \in P |-> {}]
        /\ proposal = [e \in Nat |-> <<>>]
        (* Process proc *)
        /\ height = [self \in P |-> 0]
        /\ epoch = [self \in P |-> 1]

proc(self) == /\ IF Leader(epoch[self]) = self
                    THEN /\ \E parent \in {b \in Notarized : height[self] <= Len(b)}:
                              \E txs \in TxSet:
                                LET b == Append(parent, <<epoch[self], txs>>) IN
                                  proposal' = [proposal EXCEPT ![epoch[self]] = b]
                    ELSE /\ TRUE
                         /\ UNCHANGED proposal
              /\ \/ /\ Len(proposal'[epoch[self]]) > height[self]
                    /\ vote' = [vote EXCEPT ![self] = @ \cup {proposal'[epoch[self]]}]
                    /\ height' = [height EXCEPT ![self] = Len(proposal'[epoch[self]])-1]
                 \/ /\ TRUE
                    /\ UNCHANGED <<vote, height>>
              /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************)
(* Here we define a few canary properties.  We know those properties       *)
(* should be violated at some point.  So if TLC cannot find violations, we *)
(* know there is a problem with the specification.                         *)
(***************************************************************************)
\* Find an execution in which a block is finalized:
Canary1 == \A b \in Blocks : \neg Final(b)
\* Find an execution with a final block b2 and a notarized block b1 that is incompatible with b2:
Canary2 == \neg (\E b1,b2 \in Notarized : Final(b2) /\ \neg Compatible(b1, b2))
\* Find an execution with a final chain with non-consecutive epoch numbers (needs 6 epochs):
Canary3 == \neg (\E b \in Notarized : Final(b) /\ Epoch(b) # Epoch(SubSeq(b,1,1))+Len(b)-1)
=============================================================================
\* Modification History
\* Last modified Sun Feb 05 08:45:35 PST 2023 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
