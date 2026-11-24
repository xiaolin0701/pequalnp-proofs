# Counting AND and OR gates through the quadratic part of a circuit

For the statement of L-meta-612 let G be any finite nonempty simple graph with no four-cycle. Let C be a fan-in-two monotone circuit computing its edge function. Fold constants and aliases and remove dead gates before counting parses. Write k for the number of edges for which there is no output parse consisting of the two endpoints as its only leaves, and let H be the graph obtained by removing those k edges. A parse chooses one operand at an OR and both at an AND. Leaves count with multiplicity.

**Proposition.** The conjectured bound |E(G)|+τ(G)−1 holds whenever k is zero or one. A counterexample with exactly two missing edges must have all the following properties.

* The two edges are disjoint and their deletion lowers the covering number by two. Every minimum vertex cover of H avoids their four endpoints.
* The minimum-degree homogeneous circuit is an optimal circuit for H of size |E(H)|+τ(H)−1. Exactly three gates of the normalized original circuit disappear in forming this homogeneous circuit.
* The induced graph of G on the four endpoints is the two-edge matching. The quadratic homogeneous circuit partitions the edges of H into exactly τ(H) stars, with one product per center.

These conclusions allow arbitrary non-bipartite G. They leave the unrestricted assertion in L-meta-612 open.

## Homogeneous count

The minimum-degree operation and its star count are detailed in [QuadraticInitialPart.md](../L-meta-1477/QuadraticInitialPart.md). For use here, give each leaf degree one, each AND the sum of its children's degrees, and each OR their minimum. Replace every unequal-degree OR by its lower-degree operand and remove unused gates. If H contains an edge the resulting circuit computes the homogeneous quadratic function of H. Write h for the decrease in the number of gates. Each surviving product gives the complete bipartite graph between its two variable sets, and its two sides are disjoint since the function rejects singletons. An ambient bipartition of G is unnecessary. If both sides contain two vertices this gives a four-cycle, so every product is a star. Two nontrivial linear ORs serving different centers cannot coincide or share any OR wire with two different variables: two such variables would have two distinct common neighbors, forming a four-cycle. The argument in the linked proof gives

    size(C) ≥ |E(H)| + τ(H) − 1 + h.

Equality in the homogeneous lower bound implies the number of product gates is exactly τ(H). Indeed there are at least as many distinct centers as required for a vertex cover, and with t products the bound is |E(H)|+t−1. Consequently the product centers are pairwise distinct. For each center assign its covered edges to products as in the count. If a star contained a leaf already assigned to another center, the actual number of distinct input leaves at that center would exceed its assigned count. This would strictly improve the lower bound. Thus the product stars partition E(H).

## Two gates of loss cannot account for two missing edges

Every missing edge has a successful parse on its two endpoints u,v. A bottom AND in that parse has minimum degree two, and one of its two-leaf monomials is uu, uv or vv. None can occur at the homogeneous output. That gate therefore disappears, as does some unequal-degree OR. This proves h≥2 if k>0 and H is nonempty.

If h=2, the proof in the linked note shows directly from the circuit that its original function has the form H OR (P AND Q AND R). P and Q are nonempty retained linear forms (including primary inputs), and R is the union of the opposite inputs of the products reached by the replaced lower wire. Every one of P,Q,R with at least two members has a vertex adjacent in H to all its members. A retained linear form reaches a quadratic product, and R is paired in H with the nonempty dropped OR's lower input. If a primary input among P,Q was used solely in the discarded gate, it is a singleton and need not have an H-neighbor. In the following argument, the common-neighbor property is used only for sets of size at least two.

The new two-endpoint sets supplied by the triple product lie in three rectangles,

    (P ∩ Q) × R,     (P ∩ R) × Q,     (Q ∩ R) × P.

All pairs in each rectangle are edges of G. The two sides of each are disjoint, since otherwise the original output would accept that singleton. Consider (P∩Q) × R. If |R|≥2 it has a common H-neighbor; no additional vertex can be adjacent in G to two of its elements, by the four-cycle condition. All the rectangle's pairs are therefore H-edges. If |P∩Q|≥2 apply the same argument to any two of its elements and the common H-neighbor of P. Again every pair is in H. Thus the rectangle can add a new edge only when both sides are singletons. If two rectangles add new edges, for example the first two above, Q and R must both be singletons. Both new edges must then be the pair comprising their two elements. Permutation of the factors gives the same conclusion for any pair of rectangles. Hence h=2 implies k≤1.

## Consequences for small k

If H is empty and k≤2, G has one or two edges. One edge needs an AND gate; two incident edges depend on three variables and require at least two gates. Two disjoint edges depend on four variables and require at least three gates. These are the claimed bounds or stronger and follow by counting the essential inputs of the connected binary output cone.

Suppose H is nonempty. If k=0 the homogeneous bound proves the conjecture. If k=1, deleting the edge reduces τ by at most one, and h≥2 pays for the edge and cover loss. If k=2 then h≥3. Failure of the conjectured integer bound requires τ(G)−τ(H)=2, h=3, and equality in the lower bound for the homogeneous part. A shared endpoint of the two missing edges would extend any H-cover by one vertex and is therefore impossible. If a minimum H-cover met either edge it could likewise be extended by at most one vertex. Thus every minimum H-cover avoids all four endpoints. Since such a cover covers H, H contains no edge among the endpoints and G induces exactly the matching.

