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
Thus, assuming that there are no hash collisions, a block uniquely determines all its ancestors up to the genesis block, or, equivalently, a unique sequence of epoch-payload pairs.
To model this situation, we could model a block as a recursive data structure containing its parent.
However, to make things simpler, we model a block as a sequence of pairs, each containing an epoch and a payload.
No information is lost in the process: in both cases, a block determines a unique sequence of epoch-payload pairs.

In this model of blocks, a block tree is a prefix-closed set of blocks, and a blockchain is a block tree without branching.
Moreover, extending a block `b` jeans appending an epoch-payload tuple to the block `b`.
Finally, the genesis block is the empty sequence `<<>>`.

We now define the epoch of a block `b` as `0` if `b` is the genesis block and otherwise as the epoch found in the last tuple in `b`.
In TLA+, this translates to:

```
  Epoch(b) ==
      IF b = Genesis
      THEN 0
      ELSE b[Len(b)][1]
```

Moreover, the parent of a block `b` is the genesis block if `b` has length 1, and otherwise it's the block obtained by removing the last element of `b`.
In TLA+:

```
  Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1)
```

## First specification

We start with a specification that makes use of non-determinism in order to eschew irrelevant details and capture the essence of how Streamlet ensures safety.
The specification, appearing below and in `Streamlet.tla`, is very short.
With generous formatting, it consists of a mere 44 lines of PlusCal.

```
1   --algorithm Streamlet {
2       variables
3           vote = [p \in P |-> {}], \* the vote cast by the processes,
4           proposal = [e \in E |-> <<>>];
5       define {
6           E == 1..MaxEpoch \* the set of epochs
7           Genesis == <<>>
8           Epoch(b) ==  \* the epoch of a block
9               IF b = Genesis
10              THEN 0 \* note how the root is by convention a block with epoch 0
11              ELSE b[Len(b)][1]
12          Parent(b) == IF Len(b) = 1 THEN Genesis ELSE SubSeq(b, 1, Len(b)-1) \* the parent of a block
13          Blocks == UNION {vote[p] : p \in P}
14          Notarized == {Genesis} \cup \* Genesis is considered notarized by default
15              { b \in Blocks : \E Q \in Quorum : \A p \in Q : b \in vote[p] }
16          Final(b) ==
17              /\  \E tx \in Tx : Append(b, <<Epoch(b)+1,tx>>) \in Notarized
18              /\  Epoch(Parent(b)) = Epoch(b)-1
19          Safety == \A b1,b2 \in {b \in Blocks : Final(b)} :
20              Len(b1) <= Len(b2) => b1 = SubSeq(b2, 1, Len(b1))
21      }
22      process (proc \in P)
23          variables
24              epoch = 1, \* the current epoch of p
25              height = 0; \* height of the longest notarized chain seen by p
26      {
27  l1:     while (epoch \in E) {
28              \* if leader, make a proposal:
29              if (Leader(epoch) = self) {
30                  with (parent \in {b \in Notarized : height <= Len(b) /\ Epoch(b) <= epoch},
31                          tx \in Tx, b = Append(parent, <<epoch, tx>>))
32                      proposal[epoch] := b
33              };
34              \* next, either vote for the leader's proposal or skip:
35              either {
36                  when Len(proposal[epoch]) > height;
37                  vote[self] := @ \cup {proposal[epoch]};
38                  height := Len(proposal[epoch])-1
39              } or skip;
40              \* finally, go to the next epoch:
41              epoch := epoch + 1;
42          }
43      }
44  }
```

Let me now describe the specification informally.

We have two global variables, `vote` and `proposal`, and two process-local variables, `epoch` and `height`, with the following meaning:
- For every process `p`, `vote[p]` is the set of all votes cast by `p` so far.
- For every epoch `e`, `proposal[e]` is the leader's proposal for epoch `e` unless `proposal[e]` is empty (i.e. equal to the empty sequence `<<>>`).
- For every process, the local variable `epoch` is the current epoch the process.
- For every process, the local variable `height` is the height of the longest notarized block that the process ever voted to extend.

Lines 6 to 20, we make a few useful definitions, most notably:
- Line 14, a block is notarized when a quorum unanimously voted for it.
- Line 16, a block `b` is final when:
  - line 17, `b` has a notarized child with epoch `Epoch(b)+1`, and
  - line 18, the epoch of `b`'s parent is `Epoch(b)-1`
* Finally, line 19, the algorithm is safe when every two final blocks are the same up to the length of the shortest.

Now consider a process we will call `self` at line 27, when `self` is just starting it current epoch `epoch`.

First, lines 29 to 33, if `self` is the leader of the current epoch, `self` picks a notarized block show length is greater than `height`, extends it with a new payload `tx`, and proposes it for the epoch.
This is an example of how we use non-determinism to abstract over irrelevant details:
In the original Streamlet algorithm, a process creates a proposal by extending one of the longest notarized chains it knows of.
Here we abstract over this rule by allowing the process to pick an arbitrary notarized block.
This is a sound abstraction because it does not restrict the behaviors of the algorithm (in fact, it may add new behaviors).

Next, line 35, `self` either votes for the leader's proposal or skips voting in this epoch
- Line 36, `self` checks that the proposal extends a block whose height is at least the height of last block that `self` voted to extend.
  If so, `self` votes for the proposal (line 37) and updates `height` to reflect the fact that it just voted to extend a block of height equal to the length of the proposal minus one.
- Alternatively, line 39, `self` skips voting in this epoch.
  This models the case in which `self` did not receive the leader's proposal, or the proposal is not at least of height equal to the height of the longest notarized block that `self` ever voted to extend.

Finally, line 41, `self` goes to the next epoch.

### Model-checking results

With TLC, I was able to exhaustively model-check that the `Safety` property holds for 3 processes, 2 payloads, and 6 epochs.
This was done on a 24 core `Intel(R) Xeon(R) CPU E5-2620 v2 @ 2.10GHz` with 40GB of memory allocated to TLC, and it took about 4 hours.

I think this is an interesting configuration because we have multiple quorums (sets of 2 processes at least), branching even within a single epoch (because of the 2 payloads), and enough epochs to obtain finalized chains containing non-consecutive epoch numbers and having notarized but non-final branches.
Thus, the model-checking results give me high confidence that the Streamlet algorithm is indeed safe.

## Liveness and synchronous reduction

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
