In this blog post, we'll see how to model the Streamlet algorithm in PlusCal/TLA+ with a focus on abstraction that enable tractable model-checking of both its safety and liveness properties with TLC.

# Context and results

The [Streamlet blockchain-consensus algorithm](https://eprint.iacr.org/2020/088.pdf) is arguably one of the simplest blockchain-consensus algorithm.
What makes Streamlet simple is that there are only two types of messages (leader proposals and votes) and processes repeat the same, simple propose-vote pattern ad infinitum.
In contrast, protocols like Paxos or PBFT alternate between two sub-protocols: one for the normal case, when things go well, and a view-change sub-protocol to recover from failures.

Even though I agree that Streamlet is concise, I think that understanding precisely why it works is not that simple.
Moreover, the safety proof in the [original paper](https://eprint.iacr.org/2020/088.pdf) uses the operational reasoning style, where one considers an entire execution at once and one reasons about the possible ordering of events.
In my experience, this style is very error-prone, and it's not easy to check that no case was overlooked.

Instead, I'd prefer a proof that exhibits an inductive invariant that implies safety.
This is because we only have to consider a single step, instead of an entire execution, to check whether an invariant is inductive.
For example, why Paxos works is crystal clear to me because, even though the algorithm may look more complex than in Streamlet, Paxos has a simple inductive invariant.

My overall goal was to find an inductive invariant that implies Streamlet's safety, at which point I could really say that I understand Streamlet.
To build up my intuition about the algorithm, I decided to model it in TLA+ and use the TLC model-checker to test various putative (inductive and non-inductive) invariants.
However, I haven't found an inductive invariant for Streamlet yet, and this post is about the modeling and model-checking Streamlet in TLA+.
Maybe I'll find an inductive invariant and write about it in the future.

The TLC model-checker is an explicit-state model checker, which means that it can only handle fixed configurations (e.g. 3 nodes, 5 epochs, etc.)
Moreover, TLC suffers from the state-explosion problem, where model-checking even small configurations quickly becomes intractable as the configuration size increases.

To enable TLC to check the safety and liveness of Streamlet in non-trivial system sizes, I abstracted over several aspects of Streamlet (e.g. there is no network in my model).
I believe that the abstractions I made are sound, i.e. they do not remove any behaviors, but I have not checked that mechanically.
Finally, we will also see how to exploit commutativity to soundly and drastically restrict the number of behaviors that TLC has to explore.

I was able to exhaustively check the safety and liveness properties of Streamlet in interesting configurations:
* with 3 crash-stop nodes, 2 block payloads, and 5 asynchronous epochs;
* with 3 crash-stop nodes, 2 block payloads, and 8 epochs among which the first 3 are asynchronous while the remaining 5 are synchronous (i.e. "GST" happens before epoch 4).
Even though I haven't found an inductive invariant, this gives my very high confidence that Streamlet is correct.

We'll also see that, with a small modification to the algorithm, we can guarantee that a new block gets finalized in 4 synchronous rounds (instead of 5 for the original algorithm).

# The Streamlet algorithm

The goal of the Streamlet algorithm is to enable a fixed set of `N` nodes in a message-passing network to iteratively construct a unique and ever-growing blockchain.
Although many such algorithms existed before Streamlet, Streamlet is striking because of the simplicity of the rules that nodes must follow.

Streamlet can tolerate malicious nodes, but, to simplify things, here we consider only crash-stop faults and we assume that, in every execution, a strict majority of the nodes do not fail.
As is customary, we refer to a strict majority as a quorum.

The protocol evolves in consecutive epochs (1,2,3,...) during which nodes vote for blocks according to the rules below.
A block consists of a hash of a previous block, an epoch number, and a payload (e.g. a set of transactions); moreover, a special, unique genesis block has epoch number 0.
A set of blocks forms a directed graph such that `(b1,b2)` is an edge if and only if `b2` contains the hash of block `b1`.
We say that a set of blocks forms a valid block tree when the directed graph formed by the blocks is a tree rooted at the genesis block.
A valid blockchain (or simply a chain for short) is a valid block tree in which every node has at most one successor, i.e. in which there are not forks.

Each epoch `e` has a unique, pre-determined leader (e.g. node `(e mod N)+1`), and nodes in epoch e must follow the following rules:
- The leader proposes a new block with epoch number e that extends one of the longest notarized chains that the leader knows of (where notarized is defined below).
- Every node votes for the leader's proposal as long as the proposal extends one of the longest notarized chains that the node knows of.
- A block is notarized when it has gathered votes from a quorum in the same epoch, and a chain is notarized when all its blocks (except the genesis block) are.
- When a notarized chain includes three adjacent blocks with consecutive epoch numbers, the prefix of the chain up to the second of those 3 blocks is considered final.

For example, this is a possible scenario:
* In epoch 1, the leader proposes `<< <<1, tx1>> >>` but not enough nodes receive the proposal, and `<< <<1, tx1>> >>` is not notarized.
* In epoch 2, the leader proposes `<< <<2, tx2>> >>` and `<< <<2, tx1>> >>` is notarized.
* In epoch 3, the leader proposes `<< <<3, tx3>> >>` because it hasn't yet learned that `<< <<2,tx2>> >>` is notarized; moreover, a quorum has not learned that `<< <<2,tx2>> >>` is notarized, and thus `<< <<3, tx3>> >>` is notarized.
  Note that at this point, we have two conflicting blocks of height `1` which are both notarized. However, none of those are final.
* In epoch 4, the leader has leant that `<< <<3,tx3>> >>` is notarized and makes a proposal that extends it, e.g. it proposes `<< <<3, tx3>>, <<4,tx4>> >>`.
* Epoch 5 proceeds similarly to epoch 4 and, at the end of epoch 5, `<< <<3, tx3>>, <<4,tx4>>, <<5,tx5>> >>` is notarized. Since both `<< <<3,tx3>> >>` and `<< <<3,tx3>>, <<4,tx4>> >>` are notarized, the chain `<< <<3,tx3>>, <<4,tx4>> >>` is now final.

## Safety guarantee

The algorithm guarantees that if two chains are final, then one is a prefix of the other.
This is the consistency property of the algorithm.

Note that the consistency guarantee holds even if nodes proceed through epoch at different speeds and may not be in the same epoch at the same time.

## Liveness guarantee

The Streamlet algorithm guarantees that, after 4 consecutive synchronous epochs, a new blocks gets finalized.
This is the liveness property of the algorithm.

A synchronous epoch is an epoch in which all non-faulty nodes receive each others messages before the end of the epoch, and in which the leader is not faulty.

Note that the original papers proves that we need 5 synchronous epochs with no failures to guarantee finalizing one more block, but I believe this is overly conservative and that 4 epochs suffice. Moreover, we will see that a small tweak allows to get this down to 3.

# Intuition behind the safety property

This algorithm has an interesting property: consider two maximal, notarized chains `c1` and `c2` such that the length of `c1` is smaller than the length of `c2` minus one (e.g. `c1` has length 3 and `c2` has length 5); then no block will ever be notarized on top of `c1`.

Proof:
Since `c2` is notarized, a quorum voted to extend the predecessor of `c2`, and thus all nodes in that quorum have seen a chain of length at least `length(c2)-1`.
Moreover, since nodes only vote to extend one of the longest chains they know of, those nodes will never vote to extend `c1` because, by assumption, it has a length at most `length(c2)-2`.
Thus, because two quorums intersect, no block extending `c1` will ever gather a full quorum of votes.
QED.

This shows that, when a notarized chain c becomes two blocks longer than any other chain, the other chains will never grow again and can be abandoned, and we can consider c final without risking any disagreement.

But how do nodes detect that a notarized chain has become 2 blocks longer than any other notarized chain? That it difficult to do in a distributed system because a node may not know of all the notarized blocks.
The Streamlet algorithm solves this problem using epochs: since nodes only vote once per epoch, after three consecutive epochs extending the same notarized chain c, we can be sure that c is now two blocks longer than any other chain.

Proof:
Since c gets extended, c is at most one block shorter than the longest notarized chains.
Thus, after adding three blocks to it, c is now two blocks longer than any other notarized chain.
QED.

# Streamlet in PlusCal/TLA+

# Liveness

# Remarks

[The excellent model written by Murat](https://github.com/muratdem/PlusCal-examples/blob/master/Streamlet/str0.tla) and [described in his blog](https://muratbuffalo.blogspot.com/2020/07/modeling-streamlet-in-tla.html) uses a shared-whiteboard model of messages in which all nodes learn about a new notarized chain atomically.
In contrast, in the model of the present post, nodes independently learn about new notarized chains.
Thus, I think that the model of this post more faithfully represents what can happen in an asynchronous system.

Stay tuned for a discussion of Streamlet's liveness property.
