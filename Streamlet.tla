----------------------------- MODULE Streamlet -----------------------------

EXTENDS Common

(* 
--algorithm Streamlet {
    variables
        votes = [p \in P |-> {}], \* the votes cast by the processes,
    define {
        Blocks == UNION {votes[p] : p \in P}
        Notarized(b) == 
            \/  b = Root \* we consider the root as notarized by default 
            \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
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
            \* pick a possibly new notarized block of sufficient height:
            with (b \in Blocks \cup {<<>>}) {
                when Notarized(b) /\ Len(b) >= height /\ Epoch(b) < epoch;
                height := Len(b);
                either 
                    \* pick a payload, form a new block, and vote:
                    with (tx \in Tx, newB = Append(b, <<epoch, tx>>))
                        votes[self] := @ \cup {newB};
                or
                    skip \* skip voting
            };
            epoch := epoch + 1;
        }
    }
}
*) 
\* BEGIN TRANSLATION (chksum(pcal) = "9a06292a" /\ chksum(tla) = "ff6aaabd")
VARIABLES votes, pc

(* define statement *)
Blocks == UNION {votes[p] : p \in P}
Notarized(b) ==
    \/  b = Root
    \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

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
                  THEN /\ \E b \in Blocks \cup {<<>>}:
                            /\ Notarized(b) /\ Len(b) >= height[self] /\ Epoch(b) < epoch[self]
                            /\ height' = [height EXCEPT ![self] = Len(b)]
                            /\ \/ /\ \E tx \in Tx:
                                       LET newB == Append(b, <<epoch[self], tx>>) IN
                                         votes' = [votes EXCEPT ![self] = @ \cup {newB}]
                               \/ /\ TRUE
                                  /\ votes' = votes
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
\* Last modified Tue Dec 28 22:18:38 PST 2021 by nano
\* Created Sun Dec 19 18:32:27 PST 2021 by nano
