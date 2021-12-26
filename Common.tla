------------------------------- MODULE Common -------------------------------

EXTENDS Sequences, FiniteSets, Integers

CONSTANTS
        P \* The set of processes
    ,   Tx \* Transtaction sets (the payload in a block)
    ,   MaxEpoch
    ,   Quorum \* The set of quorums
    
E == 1..MaxEpoch

(***************************************************************************)
(* Blocks and block trees                                                  *)
(***************************************************************************)

Root == <<>> \* the root of the block tree
    
\* A block is a sequence of pairs where each pair consists of an epoch and a tx set:
IsBlock(b) == 
    /\  DOMAIN b = 1..Len(b) 
    /\  \A i \in DOMAIN b : 
        /\  b[i] = <<b[i][1],b[i][2]>>
        /\  b[i][1] \in E
        /\  b[i][2] \in Tx
Epoch(b) == IF b = Root THEN 0 ELSE b[Len(b)][1]
Payload(b) == b[Len(b)][2]
Parent(b) == SubSeq(b, 1, Len(b)-1)

Prefix(b1, b2) == Len(b1) < Len(b2) /\ b1 = SubSeq(b2, 1, Len(b1)) \* strict prefix
Compatible(b1, b2) == b1 = b2 \/ Prefix(b1, b2) \/ Prefix(b2, b1)

(***************************************************************************)
(* Auxiliary definitions                                                   *)
(***************************************************************************) 
    
Num == \* assigns a process number to each process
    CHOOSE f \in [P -> 1..Cardinality(P)] : 
        \A p1,p2 \in P : p1 # p2 => f[p1] # f[p2]
Proc(n) == \* the inverse of Num
    CHOOSE p \in P : Num[p] = n

Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Min(X) == CHOOSE x \in X : \A y \in X : x <= y
Abs(n) == IF n < 0 THEN -n ELSE n

=============================================================================
\* Modification History
\* Last modified Sun Dec 26 14:53:16 PST 2021 by nano
\* Created Sun Dec 26 14:45:25 PST 2021 by nano
