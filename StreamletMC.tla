----------------------------- MODULE StreamletMC ---------------------------

\* TLC setup for Streamlet

EXTENDS Streamlet, TLC

CONSTANTS tx1, tx2, p1, p2, p3

TxSet_MC == {tx1, tx2} \* two possible blocks
P_MC == {p1,p2,p3} \* three processes
Quorum_MC == {{p1,p2},{p2,p3},{p1,p3},{p1,p2,p3}}
Leader_MC(e) == LET i == e % 3 IN
    CASE i = 0 -> p1
    []   i = 1 -> p2
    []   i = 2 -> p3
MaxEpoch == 7
Nat_MC == 0..MaxEpoch
EpochActionConstraint == \A p \in P : epoch'[p] <= MaxEpoch
Symm == Permutations({p1,p2,p3})
============================================================================