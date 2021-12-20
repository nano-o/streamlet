The Streamlet blockchain consensus algorithm is arguably one of the simplest
such algorithms.

In their presentation of the Streamlet algorithm, Shi and TODO
provide a convincing correctness proof, which nevertheless left me wanting to
understanding the algorithm on a more intuitive level.

In this post, I make a simple observation that allowed me to understand the
algorithm on a more intuitive level. More, I illustrate my reasoning with
PlusCal models and claims that can be checked with the TLC model-checker on
small instances of the problem.

```tla
RECURSIVE Distance(_,_,_)
Distance(W, v, G) == \* W is a set of vertices
    CASE
        v \in W -> 0
    []  v \in Children(W,G) -> 1
    []  OTHER -> 1 + Distance(Children(W,G), v, G)
```
