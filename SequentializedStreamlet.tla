------------------------ MODULE SequentializedStreamlet ------------------------

(***************************************************************************)
(* This is a specification of a crash-stop version of the Streamlet        *)
(* consensus algorithm.  We have sequentialized the specification in order *)
(* to make model-checking of the liveness property of Streamlet tractable. *)
(*                                                                         *)
(* For 3 processors, we are able to model-check that Streamlet decides in  *)
(* 4 synchronous epochs at most even if we first have 5 completely         *)
(* asynchronous epochs (which offers plenty of opportunity for notarized   *)
(* forks, e.g.  a fork of length 3).  That takes about 3 hours on an       *)
(* Intel i7-12700K with 64 GB of RAM.                                      *)
(*                                                                         *)
(* See the following blog post for more details:                           *)
(* https://www.losa.fr/blog/streamlet-in-tla+                              *)
(*                                                                         *)
(* Also see the file Streamlet.tla for comments on the common definitions. *)
(***************************************************************************)

EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   Quorum \* The set of quorums
    ,   GSE \* the first synchronous epoch
    ,   Leader(_) \* maps an epoch to a leader

(*
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized p voted to extend
        votes = [p \in P |-> {}], \* the votes cast by the processes
        epoch = 1, \* the current epoch
        scheduled = {}, \* the processes that have been scheduled already in the current epoch
        proposal = <<>>; \* the proposal of the leader for the current epoch
    define { \* Most of the following definitions are borrowed from Streamlet.tla; see that file for comments. 
        Genesis == <<>>
        Epoch(b) == 
            IF b = <<>>
            THEN 0
            ELSE b[Len(b)][1]
        Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1) \* the parent of a block
        Prefix(b1, b2) ==
            /\  Len(b1) <= Len(b2)
            /\  Len(b2) > 0 /\ b1 = SubSeq(b2, 1, Len(b1))
        Compatible(b1, b2) == Prefix(b1, b2) \/ Prefix(b2, b1)
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
        \* Safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Compatible(b1, b2)
        \* Liveness property; after epoch GSE, it takes at most 4 epochs to finalize a new block:
        Liveness == (epoch >= GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE
    }
    (***********************************************************************)
    (* Now we specify a global scheduler that produces sequentialized      *)
    (* executions of the algorithm.  There are way less sequentialized     *)
    (* executions than normal executions, so this makes the model-checking *)
    (* problem easier.  Moreover, we informally justify in the blog post   *)
    (* why the correctness of the sequentialized executions implies the    *)
    (* correctness of all executions.                                      *)
    (***********************************************************************)
    process (scheduler \in {"sched"})
    {
l1: while (TRUE) {
            with (proc = NextProc) {
                \* if proc is leader, make a proposal:
                if (Leader(epoch) = proc)
                    with (parent \in {b \in Notarized : height[proc] <= Len(b) /\ Epoch(b) <= epoch})
                    with (tx \in Tx)
                    with (b = Append(parent, <<epoch, tx>>)) {
                        (***************************************************)
                        (* after the first synchronous epoch, the leader   *)
                        (* is able to pick a notarized block with the      *)
                        (* highest height:                                 *)
                        (***************************************************)
                        when epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(parent);
                        proposal := b
                    };
                \* next, if possible, vote for the leader's proposal:
                either if (height[proc] < Len(proposal)) {
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
\* BEGIN TRANSLATION (chksum(pcal) = "1c67b4e1" /\ chksum(tla) = "2b8f6897")
VARIABLES height, votes, epoch, scheduled, proposal

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

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Compatible(b1, b2)

Liveness == (epoch >= GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE


vars == << height, votes, epoch, scheduled, proposal >>

ProcSet == ({"sched"})

Init == (* Global variables *)
        /\ height = [p \in P |-> 0]
        /\ votes = [p \in P |-> {}]
        /\ epoch = 1
        /\ scheduled = {}
        /\ proposal = <<>>

scheduler(self) == LET proc == NextProc IN
                     /\ IF Leader(epoch) = proc
                           THEN /\ \E parent \in {b \in Notarized : height[proc] <= Len(b) /\ Epoch(b) <= epoch}:
                                     \E tx \in Tx:
                                       LET b == Append(parent, <<epoch, tx>>) IN
                                         /\ epoch > GSE => \A b2 \in Notarized : Len(b2) <= Len(parent)
                                         /\ proposal' = b
                           ELSE /\ TRUE
                                /\ UNCHANGED proposal
                     /\ \/ /\ IF height[proc] < Len(proposal')
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

Next == (\E self \in {"sched"}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************)
(* A few invariants that we expect to hold:                                *)
(***************************************************************************)
Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ b2 \in Notarized /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
Inv3 == \A b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
Inv4 == \A b \in Blocks : b \in Notarized /\ (\E tx \in Tx : Append(b, <<Epoch(b)+1, tx>>) \in Notarized)
            => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)

(***************************************************************************)
(* A few canary properties that we expect to fail:                         *)
(***************************************************************************)
Canary1 == \A b \in Blocks : \neg Final(b)
Canary2 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Final(b2) /\ \neg Compatible(b1, b2))
Canary3 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ Len(b1) = 2 /\ proposal = b2 /\ \neg Compatible(b1,b2))
Canary4 == \neg (\E b1,b2 \in Blocks : b1 \in Notarized /\ b2 \in Notarized /\ Len(b1) = 2 /\ Len(b2) = 2 /\ \neg Compatible(b1,b2) /\ \neg Compatible(SubSeq(b1,1,1),SubSeq(b2,1,1)))
(***************************************************************************)
(* Find an execution in which we have a finalized block and a notarized    *)
(* fork of length 2 (requires GSE>=4):                                     *)
(***************************************************************************) 
Canary5 == \neg (
    /\ \E b1,b2 \in Blocks : 
        /\  Final(b1)
        /\  b2 \in Notarized
        /\  b1[1][2] # b2[1][2]
        /\  Len(b2) = 2 )
(***************************************************************************)
(* Find an execution in which we have a finalized block and a notarized    *)
(* fork of length 3 (requires GSE>=6):                                     *)
(***************************************************************************) 
Canary6 == \neg (
    /\ \E b1,b2 \in Blocks : 
        /\  Final(b1)
        /\  b2 \in Notarized
        /\  b1[1][2] # b2[1][2]
        /\  Len(b2) = 3 )


=============================================================================
\* Modification History
\* Last modified Sun Feb 05 21:21:51 PST 2023 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
