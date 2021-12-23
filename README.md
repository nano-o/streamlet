The Streamlet blockchain consensus algorithm is arguably one of the simplest such algorithms.

In [their presentation of the Streamlet algorithm](https://eprint.iacr.org/2020/088.pdf), Chan and Shi provide a convincing safety proof, which nevertheless left me wanting to understanding the algorithm on a more intuitive level.

In this post, I offer a different take on the safety of the crash-stop version of the Streamlet algorithm.
In doing so, I hope to help my readers to understand the algorithm more intuitively.
Moreover, I illustrate my reasoning with TLA+ models, including claims that can be checked with the TLC model-checker on small instances of the problem.

# The Streamlet algorithm

The goal of the Streamlet algorithm is to enable a fixed set of nodes in a message-passing network to iteratively construct a unique and ever-growing blockchain.
Although many such algorithms existed before Streamlet, Streamlet is striking because of the simplicity of the rules that nodes must follow.

Streamlet can tolerate malicious nodes, but, to simplify things, here we will consider only crash-stop failures.
We assume that we have a fixed set of N nodes and that only a strict minority of the nodes may crash.

The protocol evolves in consecutive epochs (1,2,3,...) during which nodes vote for blocks according to the rules below.
A block consists of a hash of a previous block, an epoch number, and a payload (e.g. a set of transactions); a special, unique genesis block that has epoch number 0.
A set of blocks can be seen as a directed graph such that `(b1,b2)` is an edge if and only if `b2` contains the hash of block `b1`, and a set of blocks forms a blockchain when every block is reachable from the genesis block.
Note that, with this definition, a blockchain may very well be a tree (i.e. it may contain forks).

Each epoch e has a unique, pre-determined leader (e.g. node (e mod N)+1), and nodes must follow the following rules:
- The leader proposes a new block (with epoch number e) that extends one of the longest notarized chains that the leader knows of (where notarized is defined below).
- Every node votes for the leader's proposal as long as the proposal extends one of the longest notarized chains that the node knows of.
- A block is notarized when it has gathered votes from a strict majority of the nodes in the same epoch, and a chain is notarized when all its blocks (except the genesis block) are.
- In any notarized chain including three adjacent blocks with consecutive epoch numbers, the prefix of the chain up to the second is final.

TODO: describe an interesting execution.

The algorithm guarantees that if two chains are final, then one is a prefix of the other.
In other words, there is a unique, linear, fork-less longest final chain.
This is the consistency property of the algorithm.

The Streamlet algorithm also never gets stuck; moreover, under eventual synchrony, the finalized chain is guaranteed to keep growing.
This is the liveness property of the algorithm.

The main question we will now address is: why does the consistency property hold?
Hopefully, we'll look at liveness in another post.

# Intuition behind the safety property

This algorithm has an interesting property: consider two maximal, notarized chains c1 and c2 such that the length of c1 is smaller than the length of c2 minus one (e.g. c1 has length 3 and c2 has length 5); then no block will ever be notarized on top of c1.

Proof:
Since c2 is notarized, a strict majority of the nodes voted to extend the predecessor of `c2`, and thus they all have seen a chain of length at least `length(c2)-1`.
Moreover, since nodes only vote to extend one of the longest chains they know of, those nodes will never vote to extend `c1` because it has a length strictly smaller than `length(c2)-1`.
Thus, because two strict majorities intersect, no node extending `c1` will ever gather a strict majority of votes.
QED.

This shows that, when a notarized chain c becomes two blocks longer than any other chain, we know that the other chains will never grow again and can be abandoned, and we can consider c final without risking any disagreement.

But how do nodes detect that a notarized chain has become 2 blocks longer than any other notarized chain? That it difficult to do in an asynchronous system because a node may not know of all the notarized blocks.
The Streamlet algorithm solves this problem using epochs: since nodes only vote once per epoch, after three consecutive epochs extending the same notarized chain c, we can be sure that c is now two blocks longer than any other chain.

Proof:
Since c gets extended, c is at most one block shorter than the longest notarized chains.
Thus, after adding three blocks to it, c is now two blocks longer than any other notarized chain.
QED.

# Streamlet in TLA+

# Liveness

# Remarks

[The excellent model written by Murat](https://github.com/muratdem/PlusCal-examples/blob/master/Streamlet/str0.tla) and [described in his blog](https://muratbuffalo.blogspot.com/2020/07/modeling-streamlet-in-tla.html) uses a shared-whiteboard model of messages in which all nodes learn about a new notarized chain atomically.
In contrast, in the model of the present post, nodes independently learn about new notarized chains.
Thus, I think that the model of this post more faithfully represents what can happen in an asynchronous system.

Stay tuned for a discussion of Streamlet's liveness property.
