# Depth bounds for the five-cycle with three-input majority blocks

The unrestricted monotone formula depth in L-meta-1404 is between six and seven. The target is the OR of the five products of adjacent block majority functions. A majority has depth three, its product with another majority has depth four, and a binary OR of five terms has depth three. This gives the upper bound seven.

## A general lower bound of six

The positive minimal inputs of the target select one cycle edge, then exactly two of the three bits at each of its endpoints. This gives 45 inputs. A maximal negative input selects one of the cycle's five maximal independent sets, puts all bits on its two vertices to one, and selects exactly one true bit in each of the other three blocks. This gives 135 inputs. Monotonicity makes these tests complete.

For any function, record the number p of the 45 positive tests it accepts and the number b of the 135 negative tests it rejects. If the two children have scores (p,b) and (q,c), an OR has componentwise upper bound (min(45,p+q),min(b,c)). An AND has componentwise upper bound (min(p,q),min(135,b+c)). Repeating a child at a gate implements padding, so the closure counts all depths up to the stated one.

The script first enumerates depth-two functions exactly on the 180 tests. They give 27,645 distinct signatures. The rotations and reflections of the five-cycle and the independent permutations of the three copies in each block preserve the two sets of tests. They give 135 orbits of depth-two signatures. For a depth-three gate move its first child to its orbit representative and try all 27,645 possibilities for the other child. This gives the exact depth-three Pareto frontier (all scores maximal for both coordinates). Apply the two componentwise bounds twice, discarding dominated pairs. At depth five every pair is dominated by (36,135), (44,120), or (45,108). The target pair (45,135) is excluded. This argument does not restrict where variables from different blocks may be combined.

Run with Python 3.10 or later:

    python3 depth_bounds.py

At depth six the same upper-bound relaxation reaches (45,135). The exact integer enumeration above leaves depth six versus seven unresolved.

## An explicit sound depth-six approximation

For a block i let M(i) denote its majority. Pick one of its three two-bit products arbitrarily, denoted P(i). Consider the OR of the following four terms, allowing the four named P occurrences to be chosen separately:

    M(1) AND (M(0) OR P(2))
    M(2) AND (M(1) OR P(3))
    M(3) AND (M(4) OR P(2))
    M(4) AND (M(0) OR P(3)).

Each parenthesized factor is an OR of four two-bit products and has depth three. The resulting formula has depth six. It implies the target on all 32,768 Boolean assignments. The edges 01, 12, 34 and 40 are accepted on all their minimal inputs. On edge 23, one term accepts a full row of the three-by-three grid of pair choices and another accepts a full column. Thus the formula covers 41 of the 45 positive minimal inputs. The four missing choices form a two-by-two grid.

## Exact obstruction for formulas made by taking ORs of selected pair-product stars

Consider stars in which one factor is an OR of chosen two-bit products from a single block, and the other is an OR of chosen two-bit products from its two neighboring blocks. Implement each factor by a binary OR tree over these primitive two-bit products. Combine the stars by a binary OR tree. For this specified syntax a star selecting u center pairs and v neighbor pairs takes depth at least one plus the ceiling of log2(2·max(u,v)). In a depth-six tree an indivisible subtree of depth d consumes at least 2^d of the 64 units of binary-tree capacity (the Kraft inequality). A star covers at most u·v distinct tests with u≤3, v≤6. Its possible capacities 4, 8, 16, 32 allow respectively at most 1, 4, 12, 18 tests.

A cover of 45 tests would require precisely four capacity-16 stars. To see this, start with the ideal efficiency 12 tests per 16 units, giving 48 tests at capacity 64. A capacity-32 star loses at least six from this estimate. A capacity-8 or capacity-4 star loses at least two. One such smaller star cannot fill 64 together with capacity-16 stars; leaving even four units unused costs three more. Two smaller stars already lose at least four. With four capacity-16 stars, a center choosing fewer than three pairs loses at least four, so all centers must be complete.

The distinct centers form a vertex cover of the five-cycle. With four different centers, label the missing one 0. Stars at 1 and 4 must include all three pairs of 0, leaving at most one pair for their other incident edge. To cover 12 and 34 fully, the stars at 2 and 3 must therefore use three pairs of 1 and 4, respectively. They each have room for at most one pair on the common edge 23, and a single row and a single column cannot cover a three-by-three grid. With three distinct centers, the two missing vertices must be nonadjacent. Their common neighbor needs at least two stars to cover all six of their pair choices. Each remaining center must dedicate three of its four choices to its own absent neighbor; again their mutual edge is covered by at most a row and a column. Two distinct centers cannot cover the five-cycle. This excludes depth six for the stated star syntax while allowing the majority blocks to be split into individual pair terms.
