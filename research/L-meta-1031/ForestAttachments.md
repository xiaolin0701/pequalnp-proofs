# Arbitrary forest attachments along a minimum vertex cover

Suppose H is a finite, nonempty graph for which the minimum monotone fan-in-two
size of its edge function equals |E(H)| + τ(H) − 1. Fix a minimum vertex cover
T of H. Form G by attaching arbitrary trees at vertices of T (a tree meets H
only at its root), and optionally adding disjoint forest components and isolated
vertices. Then

    MC(G) = |E(G)| + τ(G) − 1.

In particular every such G has a minimum circuit with the nonempty ownership
profile asked for in L-meta-1031. This gives arbitrarily large examples from
each cycle of length at least five. The attachment argument also works with a
core that has more than one cycle once its exact size is known.

## Gate elimination

For a nonconstant monotone function that is not a projection, simplify a
minimum circuit to two-input AND/OR gates with distinct valid inputs and no
constants or unused gates. This never increases the size. On fixing an
essential variable ℓ either way, at least one gate can be deleted: every
reader of ℓ becomes a copy or constant. If both cofactors are nonconstant,
some setting deletes at least two gates. With two readers, both simplify
under either setting. With one reader, choose its controlling value, zero
for AND and one for OR. This reader produces a constant and its next user
simplifies. It must have a user since the restricted output is nonconstant.
The same elimination is proved for circuits allowing NOT in the upstream
helpers ForestElim and PermInputs.

## A strengthened induction

For a set A of isolated variables consider the OR of their literals and f(G).
We claim its size is at least

    |A| + |E(G)| + τ(G) − 1.

The proof is by induction on edges outside H. Variables in A are isolated
from all graph edges. The base also covers any number of leaves directly
attached to T. Their addition preserves τ(H) since T still covers everything.
Set these leaves to zero one at a time, eliminating at least one gate for
each. Restrict each isolated literal in A to zero as well; every remaining
function contains the nonempty core and is nonconstant. This gives the bound.
Isolated variables outside A have no effect.

If some tree attached to T has depth at least two, choose a leaf ℓ of
largest depth and its parent p outside H. All children of p are leaves.
If there is a nontrivial disjoint tree, instead root it anywhere and apply
the same argument to a deepest leaf. Consequently either p has a second leaf
neighbor or degree at most two.

If p has another leaf neighbor, delete pℓ by setting ℓ to zero. In the
remaining graph there is an optimum cover containing p: a cover omitting
p can replace the second leaf by p without growing. This cover covers pℓ
too, so τ stays fixed. One-gate elimination and induction prove the claim.

In the remaining case let d ∈ {1,2} be the degree of p. Since p is outside H,
neither restriction below removes a core edge. The unary set A is disjoint
from the affected vertices. Both cofactors are nonconstant because the core
still contains an edge and the empty input remains false. For some b fixing
ℓ=b deletes at least two gates.

- If b=0, delete the one edge pℓ. The new cover number drops by at most one,
  as p can extend any cover of the new graph. The inductive lower bound
  decreases by at most two.
- If b=1, p becomes a positive literal. Delete all d incident edges and add
  p to A, since that literal absorbs all its edge terms. The new cover number
  drops by at most one. The inductive lower bound decreases by at most
  d+1−1=d≤2.

The smaller graphs remain in the same class. This proves the lower bound.
For A empty, the usual edge partition into stars about a minimum cover gives
the matching upper bound. Every resulting AND has no strict AND ancestor and
owns exactly the edges allocated to it.

The stronger induction adapts the good-leaf argument in the upstream proof
PEqualNP.MetaComplexity.Helpers.Forest.forest_bound. The preservation of an
arbitrary fixed core and the allowed attachment set are the additional steps.

## All graphs with exactly one cycle

For any finite graph G with exactly one cycle, of length at least five,
the above lower bound may be weakened by one *without any restriction on
the attachment points*. In symbols,

    |E(G)| + τ(G) − 2 ≤ MC(G) ≤ |E(G)| + τ(G) − 1.

To prove the lower bound, allow the isolated positive literals A as above and
induct on the number of edges outside the cycle. If there are no leaves
attached to the cycle, the core is the cycle, already exact, with disjoint
forest handled by the preceding theorem. A leaf of maximal depth with parent
off the cycle or a parent with two leaf neighbors is handled exactly as above.
Thus assume all attached trees are single leaves, each at a different cycle
vertex. Select a leaf ℓ with cycle parent p. Setting ℓ=false deletes one edge
and drops the cover number by at most one. Setting ℓ=true makes p a literal
and deletes exactly three edges. The new graph in the latter case is a
forest, so one recovers the extra gate from its exact lower bound even with
A∪{p} as isolated literals. Since one of the settings eliminates at least
two gates, both branches give the claimed bound. Disjoint forest components
can be peeled first, using the same two outside-parent reductions.

Suppose an edge-minimal graph in this class misses the upper bound. It is a
cycle with one attached leaf at each vertex of a subset W. If an off-cycle
parent remained, both restrictions in the induction would have exact lower
bounds (also after adding isolated literals by successive zero restrictions),
which would contradict the assumed deficiency. The same argument removes
disjoint forest components and repeated leaves. Every leaf in the resulting
graph has a unique reader, an OR gate. Indeed fixing a leaf to zero gives a
smaller graph whose bound is exact. If the cover number stays unchanged this
already contradicts one-gate elimination. If it drops by one, only one gate
can be eliminated on setting that leaf to zero. Two readers would both
simplify, and a unique AND reader would propagate zero to its next user and
simplify that gate too. The output cofactor is nonconstant.

If W has cardinality at most three and the cycle with its leaves has at
most eight vertices, the potentially deficient shapes from this reduction are a five-cycle with
leaves on three consecutive vertices and a six-cycle with two leaves on
vertices of opposite parity. The latter roots are not both in an alternating
minimum cover. For the latter graph the same proof
reduces a putative one-gate saving to two distinct leaves with unique OR
readers. These restrictions are necessary conditions for deficiency only.

## Eight vertices

For the five-cycle case and the two six-cycle cases (the two roots either
adjacent or antipodal), the edge count is 8 and the minimum cover size is 4.
The one-gate-gap result shows that only a 10-gate circuit could beat the
11-gate star construction. Removing any pendant edge leaves a graph of known
exact size 9, so each of the indicated leaves has a unique OR reader if the
original circuit has size 10. The graph automorphisms preserve these sets of
leaves. Run, for each indicated row:

```sh
name=cycle5threeconsecutive
python3 L-meta-1031/finite_search.py "$name" 10 "/tmp/$name.cnf" --prune-minimum --critical-leaves
cadical --lrat "/tmp/$name.cnf" "/tmp/$name.lrat.gz"
gzip -dc "/tmp/$name.lrat.gz" | lrat-trim -S --no-trim "/tmp/$name.cnf" -
```

Rows cycle5threeconsecutive, cycle6twoadjacent, and cycle6twoopposite all
returned UNSAT and independent LRAT verification succeeded in each case.
All three explicit 11-gate upper-bound circuits, every input, and their
strict ownership cones were also verified by verify_stars.py. Consequently
every graph on at most eight vertices with exactly one cycle of length at
least five satisfies the L-meta-1031 conclusion, with exact size |E|+τ−1.

## Parity of the irreducible whiskered cycles

In the candidate cycle with leaves at W, write U for the unwhiskered cycle
vertices. Then τ(G)=|W|+τ(C[U]): an optimum cover can always be chosen to
contain each root instead of its unique leaf. Deleting the leaf at p in W
changes the cover number by one precisely when adding p to C[U] leaves its
cover number unchanged. The latter requires that a minimum cover of C[U]
contain all neighbors of p in U. Indeed a cover of the old size in the
larger graph must omit p, since deleting p from such a cover would give a
cover of C[U] smaller than its minimum.

If a nonempty consecutive run of U has odd length, its path has a unique
minimum cover, consisting of every second vertex and excluding both ends.
(For 2r+1 vertices the unique independent set of size r+1 consists of the
odd positions.) The adjacent whiskered root cannot be critical. Thus in
any edge-minimal deficient graph every run of unwhiskered vertices has
even length. In particular the number of nonisolated vertices of that
graph is 2|W|+|U|, an even number. This necessary condition includes U empty;
W empty is already covered by the exact cycle bound.

Combined with the eight-vertex computation, this proves the exact bound and
the official ownership conclusion for **every graph on at most nine vertices
with exactly one cycle of length at least five**. A minimal offending graph
on at most nine vertices reduces to an even-order candidate on at most
eight nonisolated vertices, and all such candidates were excluded above.
