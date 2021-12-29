------------------------ MODULE SynchronousStreamlet ------------------------

EXTENDS Common

(* 
--algorithm Streamlet {
    variables
        height = [p \in P |-> 0], \* height of the longest notarized chain seen by p
        votes = [p \in P |-> {}], \* the votes cast by the processes
        epoch = 1, \* the current epoch
        n = 1, \* the next process to take a step
        proposal = <<>>; \* in a synchronous epoch, the proposal of the leader
    define {
        Blocks == UNION {votes[p] : p \in P}
        Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
        \* Final blocks:
        Final(b) == 
            /\  b # Root
            /\  \E tx \in Tx :
                    /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
                    /\  Epoch(Parent(b)) = Epoch(b)-1
        \* Main safety property:
        Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
        \* Liveness property; it takes at most 4 epochs to finalize a new block: 
        Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1
        \* Invariants:
        Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
        Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ Notarized(b2) /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
        Inv3 == \A b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
        Inv4 == \A b \in Blocks : Notarized(b) /\ (\E tx \in Tx : Notarized(Append(b, <<Epoch(b)+1, tx>>))) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
    }
    macro setProposal() {
        with (b \in Blocks \cup {<<>>}) { \* first pick a block to extend
            \* leader picks a notarized block:
            when Notarized(b);
            \* after the first synchronous epoch, the leader picks the notarized block with the most recent epoch:
            \* when epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Epoch(b2) <= Epoch(b);
            \* with the version of the paper, there should be a violation when GSE=5:
            when epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Len(b2) <= Len(b);
            \* TODO: why does TLC not find it?
            with (tx \in Tx)
                proposal := Append(b, <<epoch,tx>>)
        }
    }
    macro setupNextStep() {
        if (n = Cardinality(P)) {
            n := 1;
            epoch := epoch+1
        }
        else
            n := n+1
    }
    process (scheduler \in {"sched"}) \* TODO: using the proposal all the time would speed-up model-checking
    {
l1:     while (epoch \in E) {
            if (n = 1) { \* we're starting the epoch, so pick a proposal
                setProposal()
            };
            with (proc = Proc(n)) \* process number n takes a step
            either {
                \* vote for the proposal if possible
                if (height[proc] <= Len(proposal)-1) {
                    votes[proc] := @ \cup {proposal};
                    height[proc] := Len(proposal)-1;
                }
                else \* else skip the epoch
                    skip;
            }
            or { \* if before GSE, skip this epoch
                when epoch < GSE;
                skip
            };
            setupNextStep()
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a7bd4c15" /\ chksum(tla) = "fca4eb57")
VARIABLES height, votes, epoch, n, proposal, pc

(* define statement *)
Blocks == UNION {votes[p] : p \in P}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1

Inv1 == \A b \in Blocks : Final(b) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)
Inv2 == \A b1,b2 \in Blocks : Final(b1) /\ Notarized(b2) /\ Len(b2) >= Len(b1) => b1 = SubSeq(b2, 1, Len(b1))
Inv3 == \A b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Epoch(b1) < Epoch(b2) => Len(b1) <= Len(b2)
Inv4 == \A b \in Blocks : Notarized(b) /\ (\E tx \in Tx : Notarized(Append(b, <<Epoch(b)+1, tx>>))) => \E Q \in Quorum : \A p \in Q : height[p] >= Len(b)


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
                             THEN /\ \E b \in Blocks \cup {<<>>}:
                                       /\ Notarized(b)
                                       /\ epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Len(b2) <= Len(b)
                                       /\ \E tx \in Tx:
                                            proposal' = Append(b, <<epoch,tx>>)
                             ELSE /\ TRUE
                                  /\ UNCHANGED proposal
                       /\ LET proc == Proc(n) IN
                            \/ /\ IF height[proc] <= Len(proposal')-1
                                     THEN /\ votes' = [votes EXCEPT ![proc] = @ \cup {proposal'}]
                                          /\ height' = [height EXCEPT ![proc] = Len(proposal')-1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << height, votes >>
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
Tip(b) == Notarized(b) /\ \A b2 \in Blocks : Prefix(b,b2) => \neg Notarized(b2)
BaitInv1 == \A b \in Blocks : \neg Final(b)
BaitInv2 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Final(b2) /\ \neg Compatible(b1, b2))
BaitInv3 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Len(b1) = 2 /\ proposal = b2 /\ \neg Compatible(b1,b2))
BaitInv4 == \neg (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Len(b1) = 2 /\ Len(b2) = 2 /\ \neg Compatible(b1,b2) /\ \neg Compatible(SubSeq(b1,1,1),SubSeq(b2,1,1)))
BaitInv5 == \neg (
    (\E b1,b2 \in Blocks : Notarized(b1) /\ Notarized(b2) /\ Len(b1) = 2 /\ Len(b2) = 2 /\ \neg Compatible(b1,b2) /\ \neg Compatible(SubSeq(b1,1,1),SubSeq(b2,1,1)))
    /\ epoch = 6 /\ \A b \in Blocks : Notarized(b) => Epoch(b) # 5 )

=============================================================================
\* Modification History
\* Last modified Tue Dec 28 22:24:22 PST 2021 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
