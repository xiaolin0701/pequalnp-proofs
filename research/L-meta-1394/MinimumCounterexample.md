# Size required by a counterexample to the degree-four diagonal count

Any witness to L-meta-1394 must have at least 665,042 points and equally many lines in the ambient space. Its circuit size plus number of sites must be at least 1,330,083, and at least 542,673,873 diagonal incidences must be counted. These restrictions hold even when the line-degree hypotheses are dropped.

Let E be precisely the set counted in the posted statement and retain its r incident points and c incident lines. Put v = r+c, M = |E|, s = circuit size and J = number of sites. A counterexample has M positive, so both sides are nonempty. For each counted pair (p,l) choose a witnessing site. At each of that site's two root wires the value switches from false on the point-only singleton to true after adding the line l. Hence both root wires depend on l, so there is a directed path from the original line input to each root. In contrast, on the input containing only l the two roots cannot both be true, by the global soundness assumption. At least one root therefore has a directed path from the original point input as well. This dependence argument uses the actual wire evaluator, in which an unavailable wire reads a fixed false value and cannot influence a change.

Take the union of the backward cones of the pairs of roots selected this way. The two roots of every selected site belong to the same undirected connected component through their common line input. Every component contains some root, so there are at most J components. The union contains all v incident input variables. With g gate vertices and t distinct original input vertices, it has at most 2g edges by fan-in two and at least t+g−J edges by connectivity. Therefore

    v ≤ t ≤ g + J ≤ s + J.

Since 2N ≥ v, the strict inequality for a counterexample yields M > 408v. Its average degree d = 2M/v is strictly greater than 816.

Here is a direct lower bound on v for an incidence graph with no four-cycle. Put a = M/r and b = M/c. Each pair of points shares at most one line. Summing ordered pairs of neighbors of a line and applying convexity gives c b(b−1) ≤ r(r−1), hence a(b−1) ≤ r−1. Interchanging the parts gives b(a−1) ≤ c−1. Adding these inequalities and using d = 2ab/(a+b) gives

    v ≥ 2ab − a − b + 2 = 2ab(1−1/d) + 2 ≥ 2d(d−1) + 2.

The last inequality uses ab ≥ d², the arithmetic-geometric mean inequality for a and b, and d > 1. Consequently v > 1,330,082, and the stated lower bounds follow from 2N ≥ v, s+J ≥ v and the integer bound M ≥ 400v + 16⌈v/2⌉ + 1. In particular an incidence structure whose maximum degree is at most 816 cannot supply a counterexample.
