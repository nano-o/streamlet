----------------------------- MODULE Streamlet -----------------------------

EXTENDS Common

(* 
--algorithm Streamlet {
    variables
        votes = [p \in P |-> {}], \* the votes cast by the processes,
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        epoch = [p \in P |-> 1];
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
        Safety == \A b1,b2 \in Blocks : Final(b1) /\ Final(b2) /\ Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1)) 
        \* The tip of a notarized chain:
        Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)
        \* A block b is still competing if it is a tip and there is a quorum Q such that all nodes in Q have either voted for b have a height lower or equal to b (and thus b can still be notarized by this quorum).
        Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q : 
            \/  height[p] <= Len(b)
            \/  b \in votes[p]
        \* The heights of two competing blocks differ at most by 1:
        Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1 
        BaitInv1 == \A b \in Blocks : \neg Final(b)
        BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))
    }
    process (p \in P)
    {
l1:     while (TRUE) {
            either { \* proc extends a longer notarized chain with a vote
                with (b \in Blocks) { \* the notarized block we're going to extend
                    when Len(b) >= height[self] /\ Notarized(b) /\ Epoch(b) < epoch[self];
                    with (tx \in Tx, newB = Append(b, <<epoch[self], tx>>)) { \* pick a payload to form the new block
                        votes[self] := @ \cup {newB};
                    };
                    height[self] := Len(b);
                }
            } 
            or { \* proc skips the epoch
                skip
            };
            epoch[self] := @ + 1;
        }
    }
}
*) 
\* BEGIN TRANSLATION (chksum(pcal) = "71e793bd" /\ chksum(tla) = "6689cc11")
VARIABLES votes, height, epoch

(* define statement *)
Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
BlocksBefore(e) == {b \in Blocks : Epoch(b) < e}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in Blocks : Final(b1) /\ Final(b2) /\ Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)

Competing(b) == Tip(b) /\ \E Q \in Quorum : \A p \in Q :
    \/  height[p] <= Len(b)
    \/  b \in votes[p]

Inv1 == \A b1,b2 \in Blocks : Competing(b1) /\ Competing(b2) => Abs(Len(b1) - Len(b2)) <= 1
BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))


vars == << votes, height, epoch >>

ProcSet == (P)

Init == (* Global variables *)
        /\ votes = [p \in P |-> {}]
        /\ height = [p \in P |-> 0]
        /\ epoch = [p \in P |-> 1]

p(self) == /\ \/ /\ \E b \in Blocks:
                      /\ Len(b) >= height[self] /\ Notarized(b) /\ Epoch(b) < epoch[self]
                      /\ \E tx \in Tx:
                           LET newB == Append(b, <<epoch[self], tx>>) IN
                             votes' = [votes EXCEPT ![self] = @ \cup {newB}]
                      /\ height' = [height EXCEPT ![self] = Len(b)]
              \/ /\ TRUE
                 /\ UNCHANGED <<votes, height>>
           /\ epoch' = [epoch EXCEPT ![self] = @ + 1]

Next == (\E self \in P: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Dec 26 15:01:09 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
