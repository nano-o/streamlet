----------------------------- MODULE Streamlet -----------------------------

EXTENDS Common

(* 
--algorithm Streamlet {
    variables
        votes = [p \in P |-> {}], \* the votes cast by the processes,
    define {
        Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
        Notarized(b) == 
            b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
        \* Final blocks:
        Final(b) == 
            /\  b # Root
            /\  \E tx \in Tx :
                    /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
                    /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : 
            Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
    }
    process (p \in P)
        variables 
            height = 0, \* height of the longest notarized chain seen by p
            epoch = 1; \* the current epoch of p
    {
l1:     while (epoch \in E) {
            either { \* proc extends a longer notarized chain with a vote
                with (b \in Blocks) { \* the notarized block we're going to extend
                    when Len(b) >= height /\ Notarized(b) /\ Epoch(b) < epoch;
                     \* pick a payload and form the new block:
                    with (tx \in Tx, newB = Append(b, <<epoch, tx>>))
                        votes[self] := @ \cup {newB};
                    height := Len(b);
                }
            }
            or skip; \* skip this epoch
            epoch := epoch + 1;
        }
    }
}
*) 
\* BEGIN TRANSLATION (chksum(pcal) = "2d8e611" /\ chksum(tla) = "36091f03")
VARIABLES votes, pc

(* define statement *)
Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
Notarized(b) ==
    b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
    Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

VARIABLES height, epoch

vars == << votes, pc, height, epoch >>

ProcSet == (P)

Init == (* Global variables *)
        /\ votes = [p \in P |-> {}]
        (* Process p *)
        /\ height = [self \in P |-> 0]
        /\ epoch = [self \in P |-> 1]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF epoch[self] \in E
                  THEN /\ \/ /\ \E b \in Blocks:
                                  /\ Len(b) >= height[self] /\ Notarized(b) /\ Epoch(b) < epoch[self]
                                  /\ \E tx \in Tx:
                                       LET newB == Append(b, <<epoch[self], tx>>) IN
                                         votes' = [votes EXCEPT ![self] = @ \cup {newB}]
                                  /\ height' = [height EXCEPT ![self] = Len(b)]
                          \/ /\ TRUE
                             /\ UNCHANGED <<votes, height>>
                       /\ epoch' = [epoch EXCEPT ![self] = epoch[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << votes, height, epoch >>

p(self) == l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in P: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))
=============================================================================
\* Modification History
\* Last modified Mon Dec 27 15:24:47 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
