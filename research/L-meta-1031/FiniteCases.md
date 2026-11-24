# Small graphs and leaf extensions in L-meta-1031

Let f(G) be the disjunction of the edge monomials of a finite simple graph.
Size counts all fan-in-at-most-two AND and OR gates. Let τ(G) denote the vertex
cover number.

## A minimum circuit with the required ownership profile

For a nonempty graph, choose a minimum vertex cover T and assign each edge to
one of its endpoints in T. Each center in T has a neighbor outside T, by
minimality, so each assigned star is nonempty. Form the OR of its assigned
neighbors, AND with the center, and finally OR the star gates. This uses
|E|+τ−1 gates. Each AND has no strict AND ancestor. It fires on precisely its
own edges among inputs with two vertices. Thus proving the lower bound
|E|+τ−1 suffices for the official conclusion on a graph.

For forests and cycles of length at least five this lower bound is already
proved in the upstream Lean modules PEqualNP.MetaComplexity.L104 and L106.
An isolated vertex leaves minimum size unchanged: extend a circuit by
reindexing its wires, or restrict the unused variable to zero in a circuit
on the larger vertex set.

## Adding leaves without changing the cover number

Suppose the lower bound holds for G, and add a leaf at any vertex of a minimum
cover T. The new cover number is still |T|. Any minimum circuit for the new
graph can be normalized to a live DAG with no constants, two distinct valid
inputs per gate, and output at the last gate. Indeed remove dead gates,
propagate constants (including out-of-range reads), and bypass unary gates and
repeated inputs. For a nonconstant function that is not a primary projection
this introduces no gates. The new leaf is essential, so some gate reads its
wire. Set the leaf to zero. A gate reading it becomes constant or a copy,
and a circuit for G with at least one fewer gate results. The construction
above costs one additional gate, which proves optimality and star ownership.

In particular an arbitrary number of leaves can be attached to any subset of
a *fixed* minimum cycle cover. This includes a five-cycle with two leaves
attached to arbitrary cycle vertices: among the at least three other cycle
vertices there is a nonadjacent pair, whose complement is a minimum cover.

## Graphs on at most seven vertices

Delete isolated vertices. An acyclic graph is covered by L104. In the cyclic
case choose a shortest cycle, of length 5, 6 or 7. It has no chord. For length
7 it uses all vertices. For length 6 there is at most one further vertex.
If that vertex has two cycle neighbors, their distance must be 3 to avoid a
triangle or square, producing three internally disjoint paths of lengths
2,3,3 between the two neighbors. (In this case the graph has a five-cycle.)
With one attachment the graph is a cycle with a leaf.

For a five-cycle there are at most two further vertices. Neither can have two
cycle neighbors since any two cycle vertices are at distance at most 2.
If the two new vertices are not adjacent, the only additions are leaves and
isolates. If they are adjacent, their union is a separate edge, a pendant
two-edge path, or a three-edge path between two different vertices of the
five-cycle. In the final case the old endpoints must be at distance 2,
so again the three path lengths are 2,3,3. This accounts for disconnected
graphs as well.

The lower bounds for the following cases were checked on each remaining
gate count using LRAT, then matched by the explicit star circuit above.

- A five-cycle with one leaf has optimum 8. Counts 5, 6 and 7 were checked.
- A five-cycle with a pendant path of length 2 has optimum 10. Counts 6
  through 9 were checked.
- A five-cycle disjoint from an edge has optimum 9. Counts 6, 7 and 8
  were checked.

All the other cases follow from forests, cycles, isolates, and the leaf
extension except the graph with three paths of lengths 2,3,3. Its star
circuit uses 11 gates. Direct enumeration of independent sets gives τ=4. Sizes 6, 7, 8, 9 and
10 have all been excluded and independently verified. The size-10 DIMACS
instance has 690 variables and 14,744 clauses. Its compressed LRAT proof
was 444 MiB.

Consequently the official ownership conclusion holds on every graph with
at most seven vertices, with the matching exact gate lower bound in each
nonempty case.

## Exact-size encoding

The script finite_search.py uses only Python's standard library and the
small Encoding class from the sibling directory L-meta-1343. It requires
both selected input wires to precede the current gate and to be distinct,
leaves the gate type free, requires every primary input and every nonoutput
gate to be used, and fixes the last gate to the correct function on all edge
pairs and all maximal independent sets. These assignments suffice by
monotonicity. All tested example graphs have no isolated vertex.

For each gate use the key (larger input index, smaller input index).
A minimum circuit can be ordered by greedily taking the ready gate with
smallest key. The keys are then nondecreasing. Every newly ready gate reads
the gate just placed, which has a higher wire index than all previous ones.
The first gate can also be taken orbit-minimal under graph automorphisms:
among the greedy orderings of the relabelled graph choose the least first
key. Relabelling that first gate to a smaller pair leaves a ready gate with a
smaller key at the start, a contradiction. Both tests use the same key order.

If a connected live circuit uses n essential primaries and k binary gates,
its underlying DAG on n+k vertices has 2k arcs and is connected. Thus k≥n−1.
To exclude smaller-than-optimum circuits it suffices to check all exact
gate counts from n−1 up. For each size, generate the DIMACS file and run:

```sh
python3 L-meta-1031/finite_search.py cycle5leaf 7 /tmp/leaf.cnf
cadical --lrat /tmp/leaf.cnf /tmp/leaf.lrat.gz
gzip -dc /tmp/leaf.lrat.gz | lrat-trim -S --no-trim /tmp/leaf.cnf -
```

The optional flag `--prune-minimum` applies two additional necessary
conditions to minimum circuits. No gate may read both an immediate
predecessor and one of that predecessor's own inputs, as the gate can then
be bypassed by idempotency or absorption. Bypassing an AND to each one of
its inputs increases the circuit output and must introduce a false positive,
which can be extended to a maximal independent set by monotonicity. Thus
each AND must have a maximal independent set realizing its input pattern 10
and another realizing 01. Bypassing an OR instead decreases the output and
must lose a positive edge input, giving both patterns on the positive rows.
This option was omitted on all the seven-vertex instances.

The solver and independent checker used here are CaDiCaL 2.1.2 and lrat-trim
0.2.1-rc3. The solver returns status 20 and the checker prints `s VERIFIED`
for an UNSAT instance with a valid proof. Repeated runs can produce different
proofs without changing the instance.

The all-graph conclusion in L-meta-1031 still needs a proof that at least
one minimum circuit enjoys the ownership profile.
