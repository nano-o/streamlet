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
        Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
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
    }
    macro setProposal() {
        with (b \in Blocks) { \* first pick a block to extend
            \* leader picks a notarized block:
            when Notarized(b);
            \* after the first synchronous epoch, the leader the notarized block with the most recent epoch:
            when epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Epoch(b2) <= Epoch(b);
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
    process (scheduler \in {"sched"})
    {
l1:     while (epoch \in E) {
            if (n = 1 /\ epoch >= GSE) { \* we're starting a synchronous epoch; pick a proposal
                setProposal()
            };
            with (proc = Proc(n)) \* process number n takes a step
            either {
                \* before GSE:
                when epoch < GSE;
                either { \* vote
                    with (b \in Blocks) { \* the notarized block we're going to extend
                        when Len(b) >= height[proc] /\ Notarized(b);
                        with (tx \in Tx, newB = Append(b, <<epoch, tx>>))\* pick a payload to form the new block
                            votes[proc] := @ \cup {newB};
                        height[proc] := Len(b);
                    }
                }
                or { \* skip this epoch
                    skip
                }
            } 
            or {
                \* starting at GSE:
                when epoch >= GSE;
                \* vote for the proposal if possible
                if (height[proc] <= Len(proposal)-1) { \* Note that Notarized(parent) is always true 
                    votes[proc] := @ \cup {proposal};
                    height[proc] := Len(proposal)-1;
                }
                else
                    skip;
            };
            setupNextStep()
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "bcf956e" /\ chksum(tla) = "31be4db4")
VARIABLES height, votes, epoch, n, proposal, pc

(* define statement *)
Blocks == {<<>>} \cup UNION {votes[p] : p \in P}
Notarized(b) == b = Root \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]

Final(b) ==
    /\  b # Root
    /\  \E tx \in Tx :
            /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
            /\  Epoch(Parent(b)) = Epoch(b)-1

Safety == \A b1,b2 \in {b \in Blocks : Final(b)} : Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))

Liveness == (epoch = GSE+4) => \E b \in Blocks : Final(b) /\ Epoch(b) >= GSE-1


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
                  THEN /\ IF n = 1 /\ epoch >= GSE
                             THEN /\ \E b \in Blocks:
                                       /\ Notarized(b)
                                       /\ epoch >= GSE+1 => \A b2 \in Blocks : Notarized(b2) => Epoch(b2) <= Epoch(b)
                                       /\ \E tx \in Tx:
                                            proposal' = Append(b, <<epoch,tx>>)
                             ELSE /\ TRUE
                                  /\ UNCHANGED proposal
                       /\ LET proc == Proc(n) IN
                            \/ /\ epoch < GSE
                               /\ \/ /\ \E b \in Blocks:
                                          /\ Len(b) >= height[proc] /\ Notarized(b)
                                          /\ \E tx \in Tx:
                                               LET newB == Append(b, <<epoch, tx>>) IN
                                                 votes' = [votes EXCEPT ![proc] = @ \cup {newB}]
                                          /\ height' = [height EXCEPT ![proc] = Len(b)]
                                  \/ /\ TRUE
                                     /\ UNCHANGED <<height, votes>>
                            \/ /\ epoch >= GSE
                               /\ IF height[proc] <= Len(proposal')-1
                                     THEN /\ votes' = [votes EXCEPT ![proc] = @ \cup {proposal'}]
                                          /\ height' = [height EXCEPT ![proc] = Len(proposal')-1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << height, votes >>
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

=============================================================================
\* Modification History
\* Last modified Mon Dec 27 15:28:47 PST 2021 by nano
\* Created Fri Dec 24 15:33:41 PST 2021 by nano
