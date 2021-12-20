------------------------------ MODULE DiGraph ------------------------------

EXTENDS Naturals

Vertices(G) == G[1]
Edges(G) == G[2]
IsDigraph(G) ==
    /\  G = <<Vertices(G), Edges(G)>>
    /\  Edges(G) \subseteq (Vertices(G) \times Vertices(G))
    
Children(W, G) == UNION {{w \in Vertices(G) : <<v,w>> \in Edges(G)} : v \in W} 

AddEdge(v, w, G) ==
    LET Vs == Vertices(G) \cup {w}
        Es == Edges(G) \cup {<<v,w>>} 
    IN <<Vs, Es>>
            
RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, G) ==
    /\  v1 \in Vertices(G) /\ v2 \in Vertices(G)
    /\  \/  v1 = v2
        \/  <<v1,v2>> \in Edges(G)
        \/  \E v3 \in Children({v1}, G) : Reachable(v3, v2, G)
        
RECURSIVE ReachableSet(_,_)
 ReachableSet(W,G) == \* W is a set of vertices
    LET C == Children(W, G) IN 
        IF C = {}
        THEN W
        ELSE W \cup {ReachableSet(C,G)}
        
Compatible(v, w, G) == Reachable (v, w, G) \/ Reachable(w, v, G)

RECURSIVE Distance(_,_,_)
Distance(W, v, G) == \* W is a set of vertices
    CASE
        v \in W -> 0
    []  v \in Children(W,G) -> 1
    []  OTHER -> 1 + Distance(Children(W,G), v, G)

=============================================================================
\* Modification History
\* Last modified Sun Dec 19 18:33:42 PST 2021 by nano
\* Created Sun Dec 19 18:33:30 PST 2021 by nano
