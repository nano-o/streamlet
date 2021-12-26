The [Streamlet blockchain-consensus algorithm](https://eprint.iacr.org/2020/088.pdf) is arguably one of the simplest blockchain-consensus algorithms.
In this blog post, we'll see how to model the algorithm in PlusCal/TLA+ and model-check both its safety and liveness properties with TLC.
This will involve making abstraction and applying reductions in order to make the model-checking problem tractable.
Along the way, we'll make a safety argument slightly different from the original paper and we'll see that, with a small modification, it only takes at most 3 synchronous rounds for the algorithm to terminate (instead of the upper bound of 5 rounds proved in the original paper).

<!-- In order to get a good understanding of the algorithm, I decided to model it in TLA+ and to model-check both its safety and liveness properties with TLC. -->
<!-- In [their presentation of the Streamlet algorithm](https://eprint.iacr.org/2020/088.pdf), Chan and Shi provide convincing proofs; nevertheless left me wanting to understanding the algorithm on a more intuitive level. -->

<!-- In this post, I offer a different take on the safety of the crash-stop version of the Streamlet algorithm. -->
<!-- In doing so, I hope to help my readers to understand the algorithm more intuitively. -->
<!-- Moreover, I illustrate my reasoning with TLA+ models, including claims that can be checked with the TLC model-checker on small instances of the problem. -->

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
