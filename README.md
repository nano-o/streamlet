In this blog post, we'll see how to model the Streamlet algorithm in PlusCal/TLA+ with a focus on abstraction that enable tractable model-checking of both its safety and liveness properties with TLC.

# Context and results

The [Streamlet blockchain-consensus algorithm](https://eprint.iacr.org/2020/088.pdf) is arguably one of the simplest blockchain-consensus algorithm.
What makes Streamlet simple is that there are only two types of messages (leader proposals and votes) and processes repeat the same, simple propose-vote pattern ad infinitum.
In contrast, protocols like Paxos or PBFT alternate between two sub-protocols: one for the normal case, when things go well, and a view-change sub-protocol to recover from failures.

Even though Streamlet is concise, I think that understanding precisely why it works is not that simple.
Moreover, the safety proof in the [original paper](https://eprint.iacr.org/2020/088.pdf) uses the operational reasoning style, where one considers an entire execution at once and one reasons about the possible ordering of events.
In my experience, this style is very error-prone, and it's not easy to check that no case was overlooked.

Instead, I'd prefer a proof that exhibits an inductive invariant that implies safety.
This is because we only have to consider a single step, instead of an entire execution, to check whether an invariant is inductive, and thus it's easier to not miss a case.
For example, why Paxos is safe is crystal clear to me because, even though the algorithm may look more complex than Streamlet, Paxos has a simple inductive invariant that I can easily check.

My initial goal was to find an inductive invariant that implies Streamlet's safety, at which point I could really say that I understand Streamlet.
To build up my intuition about the algorithm, I decided to model it in TLA+ and use the TLC model-checker to test various scenarios and putative (inductive and non-inductive) invariants.

I haven't found an inductive invariant for Streamlet yet, and this post is about the modeling and model-checking Streamlet in TLA+.
Maybe I'll find an inductive invariant  in the future and write about it.

## Model-checking with TLC

The TLC model-checker is an explicit-state model checker, which means that it can only handle fixed configurations (e.g. 3 processes, 5 epochs, etc.)
Moreover, TLC suffers from the state-explosion problem, where model-checking even small configurations quickly becomes intractable as the configuration size increases.

To enable TLC to check the safety and liveness of Streamlet in interesting configurations, I abstracted over several aspects of Streamlet (e.g. there is no network in my model).
I believe that the abstractions I made are sound, i.e. they do not remove any behaviors, but I have not checked that mechanically.
Finally, I have also applied a reduction base on commutativity to soundly and drastically restrict the number of behaviors that TLC has to explore.

TODO: the model is in-between crash-stop and Byzantine: in asynchronous rounds, the leader can issue malicious proposals.

I was able to exhaustively check the safety and liveness properties of Streamlet in interesting configurations:
* with 3 crash-stop processes, 2 block payloads, and 5 asynchronous epochs;
* with 3 crash-stop processes, 2 block payloads, and 8 epochs among which the first 3 are asynchronous while the remaining 5 are synchronous (i.e. "GST" happens before epoch 4).
Even though I haven't found an inductive invariant, this gives my very high confidence that Streamlet is correct.

We'll also see that, with a small modification to the algorithm, we can guarantee that a new block gets finalized in 4 synchronous rounds (instead of 5 for the original algorithm).

# The Streamlet algorithm

The goal of the Streamlet algorithm is to enable a fixed set of `N` processes in a message-passing network to iteratively construct a unique and ever-growing blockchain.
Although many such algorithms existed before Streamlet, Streamlet is striking because of the simplicity of the rules that processes must follow.

Streamlet can tolerate malicious, Byzantine processes, but, to simplify things, here we consider only crash-stop faults and we assume that, in every execution, a strict majority of the processes do not fail.
However, we abstract the proposal process in such a way as to model Byzantine proposals which, in my opinion, captures the worst that Byzantine processes can do.
As is customary, we refer to a strict majority as a quorum.

The protocol evolves in consecutive epochs (1,2,3,...) during which processes vote for blocks according to the rules below.
A block consists of a hash of a previous block, an epoch number, and a payload (e.g. a set of transactions); moreover, a special, unique genesis block has epoch number 0.

A set of blocks forms a directed graph such that `(b1,b2)` is an edge if and only if `b2` contains the hash of block `b1`.
We say that a set of blocks forms a valid block tree when the directed graph formed by the blocks is a tree rooted at the genesis block.
A valid blockchain (or simply a chain for short) is a valid block tree in which every process has at most one successor, i.e. in which there are not forks.

Each epoch `e` has a unique, pre-determined leader (e.g. process `(e mod N)+1`), and processes in epoch e must follow the following rules:
- The leader proposes a new block with epoch number e that extends one of the longest notarized chains that the leader knows of (where notarized is defined below).
- Every process votes for the leader's proposal as long as the proposal extends one of the longest notarized chains that the process knows of.
- A block is notarized when it has gathered votes from a quorum in the same epoch, and a chain is notarized when all its blocks (except the genesis block) are.
- When a notarized chain includes three adjacent blocks with consecutive epoch numbers, the prefix of the chain up to the second of those 3 blocks is considered final.

For example, this is a possible scenario:
* In epoch 1, the leader proposes `<< <<1, tx1>> >>` but not enough processes receive the proposal, and `<< <<1, tx1>> >>` is not notarized.
* In epoch 2, the leader proposes `<< <<2, tx2>> >>` and `<< <<2, tx1>> >>` is notarized.
* In epoch 3, the leader proposes `<< <<3, tx3>> >>` because it hasn't yet learned that `<< <<2,tx2>> >>` is notarized; moreover, a quorum has not learned that `<< <<2,tx2>> >>` is notarized, and thus `<< <<3, tx3>> >>` is notarized.
  Note that at this point, we have two conflicting blocks of height `1` which are both notarized. However, none of those are final.
* In epoch 4, the leader has leant that `<< <<3,tx3>> >>` is notarized and makes a proposal that extends it, e.g. it proposes `<< <<3, tx3>>, <<4,tx4>> >>`.
* Epoch 5 proceeds similarly to epoch 4 and, at the end of epoch 5, `<< <<3, tx3>>, <<4,tx4>>, <<5,tx5>> >>` is notarized. Since both `<< <<3,tx3>> >>` and `<< <<3,tx3>>, <<4,tx4>> >>` are notarized, the chain `<< <<3,tx3>>, <<4,tx4>> >>` is now final.

TODO: depict graphically

## Safety guarantee

The algorithm guarantees that if two chains are final, then one is a prefix of the other.
This is the consistency property of the algorithm.

Note that the consistency guarantee holds even if processes proceed through epoch at different speeds and may not be in the same epoch at the same time.

## Liveness guarantee

The Streamlet algorithm guarantees that, after 4 consecutive synchronous epochs, a new blocks gets finalized.
This is the liveness property of the algorithm.

A synchronous epoch is an epoch in which all non-faulty processes receive each others messages before the end of the epoch, and in which the leader is not faulty.

Note that the original papers proves that we need 5 synchronous epochs with no failures to guarantee finalizing one more block, but I believe this is overly conservative and that 4 epochs suffice. Moreover, we will see that a small tweak allows to get this down to 3.

# Streamlet in PlusCal/TLA+

## Blocks

Processes in the Streamlet algorithm can be seen as building a block tree out of which emerges a unique, finalized blockchain.
Thus, we need to model blocks, block trees, and blockchains.

Except for the genesis block, a block consists of the hash of its parent block, an epoch, and a payload.
Thus, if we assume that there are no hash collisions, a block uniquely determines all its ancestors up to the genesis block.
We could model a block as a recursive data structure, but, to simplify the spec, we model a block as a sequence of pairs, each containing an epoch and a payload.

With this model of blocks, a block tree is just a set of blocks, and a blockchain and a block are the same thing.
Moreover, extending a block just means appending an epoch-payload tuple to the block.

## First specification

We start with a very simple specification which completely abstracts over leaders.
The specification is very short, as it consists of a mere 36 lines of PlusCal with generous formatting:

```
1 --algorithm Streamlet {
2     variables
3         votes = [p \in P |-> {}], \* the votes cast by the processes,
4     define {
5         Blocks == UNION {votes[p] : p \in P}
6         Notarized(b) ==
7             \/  b = <<>>
8             \/ \E Q \in Quorum : \A p \in Q : b \in votes[p]
9         Final(b) ==
10              /\  b # <<>> \* we consider the root notarized by default
11              /\  \E tx \in Tx :
12                      /\  Notarized(Append(b, <<Epoch(b)+1,tx>>))
13                      /\  Epoch(Parent(b)) = Epoch(b)-1
14            Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
15                Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
16        }
17        process (p \in P)
18            variables
19                height = 0, \* height of the longest notarized chain seen by p
20                epoch = 1; \* the current epoch of p
21        {
22    l1:     while (epoch \in E) {
23                either { \* proc extends a longer notarized chain with a vote
24                    with (b \in Blocks \cup {<<>>}) { \* pick a block to extend
25                        when Len(b) >= height /\ Notarized(b) /\ Epoch(b) < epoch;
26                         \* pick a payload and form the new block:
27                        with (tx \in Tx, newBlock = Append(b, <<epoch, tx>>))
28                            votes[self] := @ \cup {newBlock}; \* cast a vote
29                        height := Len(b);
30                    }
31                }
32                or skip; \* skip this epoch
33                epoch := epoch + 1;
34            }
35        }
36    }
```

The most interesting aspect of the specification is how we abstract over network communication while faithfully modeling the asynchronous nature of the system.
We now explain this below.

Note that for every process `p`, the global variable `votes[p]` contains the set of all votes cast by `p`.
Moreover, processes keep track of their current epoch in the local variable `e` and of the height of the longest block they every voted to extend in local variable `height`.
Now consider process `self` executing epoch `e`.
At line 23, `self` either casts a vote or entirely skips epoch `e`.
Skipping the epoch, at line 32, models the case in which `self` does not hear from the leader of epoch `e`, times out, and goes to the next epoch without voting.
If `self` does not skip epoch `e`, it executes line 24 to 29.
Line 24 and 25, `self` picks a block `b` to extend such that `b` is notarized and the length of `b` is greater or equal than the node's `height` variable.
Lines 27 and 28, `self` picks an arbitrary payload `tx`, creates a new block `newBlock` with epoch `e` and payload `tx` extending `b`, and votes for `newBlock`.
Finally, line 29, `self` updates its `height` variable to make sure that it will from now on only extend blocks of length at least equal to the length of `b`.

Note that, at line 25, we also require that `b`'s epoch be strictly smaller than `e`, and this constraint is not in the Streamlet paper.
As we will see later, this additional constraint allows thinking of the algorithm as proceeding in synchronous rounds, which we can use to speed up model-checking significantly.
Moreover, it doesn't hurt the protocol in any way. (TODO: confirm with TLC that not doing it is safe).

## Leaders

Leaders in Streamlet only help liveness, and for our first model we will only look at Safety.
So, we do not model leaders at all in this first model, and instead we let nodes vote an arbitrary notarized block whose height is greater or equal to the height of the last block that the node extended.

## Communication

We do not model the network explicitly.
Instead, for every process `p`, a global variable `votes[p]` corresponds to the set of votes cast by `p`.
Then, we define `Blocks` as the set of all votes by all processes, i.e. `Blocks == UNION {votes[p] : p \in P}`

## First specification

At this point we obtain the specification in `Streamlet.tla`

## Synchrony reduction

We exploit commutativity to reorder actions in a canonical order.

# Liveness

We assume that epoch `GSE` (for global synchronization epoch)  and all epochs after are synchronous.
In a synchronous epoch, the leader follows the algorithm, every node receives the leader's proposal, and every node receives all the votes of the other nodes (even votes cast in previous epochs).
This is reflected as follows in the TLA+ model:
* In epoch `GSE` and after, nodes vote for the leader's proposal.
* In epoch `GSE`, the leader makes a proposal, but it doesn't necessarily extend a longest notarized chain.
  This is because, at the time of making the proposal, the leader may not have received all previous votes yet.
* In epoch `GSE+1` and above, the leader proposes to extend one of the longest notarized chains.

# Remarks

[The excellent model written by Murat](https://github.com/muratdem/PlusCal-examples/blob/master/Streamlet/str0.tla) and [described in his blog](https://muratbuffalo.blogspot.com/2020/07/modeling-streamlet-in-tla.html) uses a shared-whiteboard model of messages in which all processes learn about a new notarized chain atomically.
In contrast, in the model of the present post, processes independently learn about new notarized chains.
Thus, I think that the model of this post more faithfully represents what can happen in an asynchronous system.
