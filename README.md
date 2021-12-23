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
A set of blocks can be seen as a directed graph such that `(b1,b2)` is an edge if and only if `b2` contains the hash of block `b1`, and a set of blocks forms a valid blockchain when every block is reachable from the genesis block.
Note that, with this definition, a blockchain may very well be a tree (i.e. it may contain forks).

Each epoch has a unique, pre-determined leader (e.g. the leader of epoch i is node (i mod N)+1, where N is the number of nodes).
In each epoch e, the nodes must follow the following rules:
- The leader proposes a new block (with epoch number e) that extends one of the longest notarized chains that the leader knows of (where notarized is defined below).
- Every node votes for the leader's proposal as long as the proposal extends one of the longest notarized chains that the node knows of.
- A block is notarized when it has gathered votes from a strict majority of the nodes in the same epoch, and a chain is notarized when all its blocks are.
- In any notarized chain including three adjacent blocks with consecutive epoch numbers, the prefix of the chain up to the second is final.

TODO: describe an interesting execution.

The algorithm guarantees that if two chains are final, then one is a prefix of the other.
In other words, there is a unique, linear, fork-less longest final chain.
This is the consistency property of the algorithm.

The Streamlet algorithm also never gets stuck; moreover, under eventual synchrony, the finalized chain is guaranteed to keep growing.
This is the liveness property of the algorithm.

The main question we will now address is: why does the consistency property hold?
Hopefully, we'll look at liveness in another post.

# An even simpler algorithm

To understand why Streamlet's consistency property holds, let us consider an even simpler algorithm that I call the pre-Streamlet algorithm.
This algorithm has no epochs and no leaders.
Instead, every node repeatedly does the following:
- Pick a notarized chain whose length is greater or equal to the length of every chain that the node has picked so far.
- Vote for an arbitrary block that extends the chain just picked.
As before, we say that a block is notarized when a strict majority of the nodes have voted for it.

This algorithm has an interesting property: consider two maximal, notarized chains c1 and c2 such that the length of c1 is smaller than the length of c2 minus one (e.g. c1 has length 3 and c2 has length 5); then no block will ever be notarized on top of c1.

# Back to Streamlet

As we have observed, in the pre-Streamlet algorithm, if we have two maximal, notarized chains c1 and c2 such that the length of c1 is smaller than the length of c2 minus one (e.g. c1 has length 3 and c2 has length 5), then no block will ever be notarized on top of c1.
Thus, when a notarized chain c becomes two blocks longer than any other chain, we know that the other chains will never grow again and can be abandoned, and we can consider c final without risking any disagreement.

But how do nodes detect that a chain has become 2 blocks longer than any other chain? That it difficult to do in an asynchronous system because a node may not know of all the notarized blocks.
The Streamlet algorithm solves this problem using epochs: since nodes only vote once per epoch, after three consecutive epochs extending the same notarized chain c, we can be sure that c is now two blocks longer than any other chain.
This is because, since c gets notarized, it is at most one block shorter than the longest notarized chains. Thus, after adding three blocks to it, c is now two blocks longer than any other chain.

# Remarks

[The excellent model written by Murat](https://github.com/muratdem/PlusCal-examples/blob/master/Streamlet/str0.tla) and [described in his blog](https://muratbuffalo.blogspot.com/2020/07/modeling-streamlet-in-tla.html) uses a shared-whiteboard model of messages in which all nodes learn about a new notarized chain atomically.
In contrast, in the model of the present post, nodes independently learn about new notarized chains.
Thus, I think that the model of this post more faithfully represents what can happen in an asynchronous system.

Stay tuned for a discussion of Streamlet's liveness property.

# TLC counter-example in PreStreamlet

```
Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate>
/\ height = (p1 :> 0 @@ p2 :> 0 @@ p3 :> 0)
/\ votes = (p1 :> {<<v1, v3>>, <<v1, v5>>} @@ p2 :> {<<v1, v3>>} @@ p3 :> {<<v1, v5>>})

State 2: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 0 @@ p3 :> 0)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>} @@
  p3 :> {<<v1, v5>>} )

State 3: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>, <<v3, v2>>} @@
  p3 :> {<<v1, v5>>} )

State 4: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>, <<v3, v2>>, <<v5, v6>>} @@
  p3 :> {<<v1, v5>>} )

State 5: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 2 @@ p3 :> 0)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>, <<v3, v2>>, <<v5, v6>>, <<v6, v4>>} @@
  p3 :> {<<v1, v5>>} )

State 6: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 2 @@ p3 :> 2)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>, <<v3, v2>>, <<v5, v6>>, <<v6, v4>>} @@
  p3 :> {<<v1, v5>>, <<v6, v4>>} )

State 7: <proc line 120, col 15 to line 124, col 71 of module PreStreamlet>
/\ height = (p1 :> 1 @@ p2 :> 2 @@ p3 :> 2)
/\ votes = ( p1 :> {<<v1, v3>>, <<v1, v5>>, <<v3, v2>>, <<v5, v6>>} @@
  p2 :> {<<v1, v3>>, <<v3, v2>>, <<v5, v6>>, <<v6, v4>>} @@
  p3 :> {<<v1, v5>>, <<v6, v4>>} )
```

# TLC counter-example in Streamlet

```
State 1: <Initial predicate>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<>>, <<>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<>>, <<>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 4 @@ p2 :> 3 @@ p3 :> 4)

State 2: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<>>, <<>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 5 @@ p2 :> 3 @@ p3 :> 4)

State 3: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<>>, <<>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 6 @@ p2 :> 3 @@ p3 :> 4)

State 4: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<v3, v2>>, <<>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 6 @@ p2 :> 4 @@ p3 :> 4)

State 5: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<v3, v2>>, <<v3, v2>>, <<>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 6 @@ p2 :> 5 @@ p3 :> 4)

State 6: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 0)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<v3, v2>>, <<v3, v2>>, <<v5, v4>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<>>, <<>>>> )
/\ round = (p1 :> 6 @@ p2 :> 6 @@ p3 :> 4)

State 7: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 1)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<v3, v2>>, <<v3, v2>>, <<v5, v4>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<v3, v2>>, <<>>>> )
/\ round = (p1 :> 6 @@ p2 :> 6 @@ p3 :> 5)

State 8: <proc line 144, col 15 to line 150, col 70 of module Streamlet>
/\ height = (p1 :> 0 @@ p2 :> 1 @@ p3 :> 1)
/\ votes = ( p1 :> <<<<v1, v3>>, <<>>, <<v1, v5>>, <<v1, v3>>, <<v1, v3>>>> @@
  p2 :> <<<<v1, v3>>, <<v3, v2>>, <<v3, v2>>, <<v3, v2>>, <<v5, v4>>>> @@
  p3 :> <<<<>>, <<>>, <<v1, v5>>, <<v3, v2>>, <<v5, v4>>>> )
/\ round = (p1 :> 6 @@ p2 :> 6 @@ p3 :> 6)


```
