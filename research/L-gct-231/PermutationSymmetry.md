# A three-dimensional solution would have trivial simultaneous permutation stabilizer

Suppose a complex linear three-space of symmetric \(4\times4\) matrices satisfies \(\operatorname{per}(J+X)=24\) identically. No nonidentity permutation of the four labels can preserve the space by simultaneous row and column permutation.

Write \(r_j\) for the sum of all size-\(j\) matchings. By homogeneity the equations are \(r_1=r_2=r_3=r_4=0\). On the nine-dimensional space of symmetric matrices of total sum zero, \(r_2\) is nondegenerate in characteristic 13. Explicitly, write the matrix as \(X_{ij}=b_i+b_j+D_{ij}\), with \(\sum b_i=0\) and zero row and column sums in \(D\). Then \(r_2=\frac12\sum D_{ij}^2-12\sum b_i^2\). The two forms are nondegenerate: the zero-sum three-space is nondegenerate and its symmetric tensor square has nondegenerate induced form in odd characteristic. The same applies in characteristic zero.

**Involutions.** In odd characteristic a stable subspace decomposes into its positive and negative eigenspaces. The ambient eigenspaces are orthogonal complements, so both have nondegenerate second matching form and their isotropic dimensions are at most half their dimensions. For a single transposition the dimensions on the tangent space are \((6,3)\), allowing splits \((3,0),(2,1)\). For a double transposition the dimensions are \((5,4)\), allowing splits \((2,1),(1,2)\). For each split use echelon-form bases independently in each eigenspace. Each pivot set specifies a Schubert cell; entries to the left of a row pivot or in other pivot columns are fixed at zero, and the pivot is one. All remaining entries are independent variables. For each cell, substitute the three universal basis vectors into all polarizations of \(r_2,r_3,r_4\). In characteristic 13 the 65 single-transposition cell ideals and the 70 double-transposition cell ideals all have reduced Gröbner basis \([1]\). These counts include all legal pivot sets in the four listed splits, over the algebraic closure.

**Three-cycles.** Use characteristic seven and a primitive cube root \(2\). The eigenvalue-one tangent block has dimension three, consisting of common diagonal and triangle-edge values in the moving triple, a common edge value to the fixed vertex, and the unique final diagonal enforcing total sum zero. Its three homogeneous matching equations have zero-dimensional affine vanishing set, hence no nonzero fixed vector. Each of the two nontrivial weight blocks also has dimension three. Only the cubic equation survives on such a block. The homogeneous Jacobian ideal has affine dimension zero for both blocks, so these projective cubics are smooth. A smooth plane cubic over an algebraically closed field has no line component, by Bézout. Thus a stable solution can use at most one dimension from each nontrivial block and none from the fixed block.

A four-cycle has an involution as its square. Independently, the four-cycle script in characteristic thirteen shows that the fixed block has no nonzero level direction, each nontrivial block can contribute at most one dimension, and the twelve affine pivot charts for one line from each nontrivial block are empty. For every permutation tested, the stable-plane equations define a closed subset of the Grassmannian over the integers; its projection to the integer spectrum is proper. Emptiness of one geometric special fiber excludes a complex stable three-space.

The programs use Python with SymPy and Singular. From this directory run

```sh
python3 check_involutions.py --singular Singular
python3 check_cycles.py 3 > /tmp/gct231-cycle3.sing
Singular -q /tmp/gct231-cycle3.sing
python3 check_cycles.py 4 > /tmp/gct231-cycle4.sing
Singular -q /tmp/gct231-cycle4.sing
```

The unrestricted finite-field counts in [the independent residue search](check_residue_planes.cpp) also rule out solutions defined over number fields having a residue-degree-one prime above five, seven, or thirteen. The quadratic-extension search below rules out every number field of degree at most two.

## No plane over a quadratic number field

Let a three-plane be defined over a number field, and fix a prime over five. In a three-row basis matrix choose a nonzero three-column minor with minimal valuation. Left-multiply by the inverse of that minor. The three pivot columns are now the identity, and each remaining entry is a signed ratio of minors. All entries are integral at the chosen prime. Reduction therefore preserves linear independence. The coefficients of the permanent in three formal parameters are polynomial identities over the valuation ring, so every reduced matrix on the plane also has permanent 24 after translation by the all-ones matrix.

The residue degree of a quadratic number field at five is one or two. Both residue fields embed into the field with 25 elements. Enumerating this field gives 18,610 normalized directions with entries at positions 0 and 1 zero, followed by 539 compatible pairs and zero independent, pairwise compatible triples in the pivot search. A three-plane would contain such a triple. This excludes every quadratic number field, including cases where five ramifies. An independent implementation enumerating the nonattacking two-rook placements and all 24 permutation products reproduced the five cut counts and the 539 pairs, with no independent triangle. The implementation is in [check_quadratic_residue.cpp](check_quadratic_residue.cpp).

Over the field with 49 elements the five cut sizes are 128,942, 125,960, 120,943, 126,025, and 122,172. Of 1,130 compatible pairs, two independent pairwise-compatible triples survive, and neither span is a level space. Thus every prime above five or seven in any field of definition has residue degree at least three. Over each prime field of order 11, 17, 19, 23, 29 and 31 the same enumeration also returned no independent triangle.

As a cross-check, the same enumeration over the field with nine elements gives 18,148 pairs, 172,206 independent triangles and 172,192 fully compatible ordered bases in the pivot search. The direct permutation-and-support enumeration gives identical counts. Over the prime field with five elements the two implementations both give 136 anchors, 65 pairs and zero triangles.

## Maximality of the two-dimensional symmetric hook

Consider the span of the matrices supported in row and column zero, with central entry zero and off-diagonal row entries \(x,y,-x-y\). It is two-dimensional, and the permanent is identically 24 after translation. If a complex symmetric level space contains the whole hook, then it equals the hook. A new direction would have to make all six permanental cofactors of its translated lower three-by-three block equal. The coefficients of first order in the direction force the six lower-block entries to agree. A parameter value making this common block vanish rules out any nonzero common entry. The remaining permanent identity forces the central entry and the sum of the three off-diagonal row entries to vanish as well. [HookMaximal.lean](HookMaximal.lean)

Every nonzero direction of any such complex space has ordinary matrix rank at least two. For an outer square \(vv^T\), the coefficient of \(t^k\) in the permanent of \(J+t vv^T\) is \(k!(4-k)!e_k(v)^2\). Constant permanent forces every elementary symmetric polynomial of the four coordinates to vanish, hence all four coordinates are zero. A symmetric rank-one factorization is proportional to an outer square. [RankOneObstruction.lean](RankOneObstruction.lean)

## A candidate must have a direction of rank at least three

The following argument uses complex projective geometry in addition to the rank-one lemma above. Suppose a candidate consisted entirely of matrices of rank at most two. Its projectivization is a complex projective plane of quadratic forms, each a product of two distinct linear forms. Ordering the distinct factors gives an unramified double cover of this plane, by pulling back the ordered-pair cover of the distinct-factor locus in the symmetric square of the dual projective three-space. Complex projective space is simply connected, so this cover splits. The two resulting factor maps pull back the hyperplane bundles to \(\mathcal O(a)\) and \(\mathcal O(b)\) with nonnegative degrees. Their tensor product is \(\mathcal O(1)\), since multiplication of the factors recovers the given linear plane. One factor has degree zero and is constant. Hence all the matrices have the form \(uv^T+vu^T\) for a fixed nonzero \(u\), with \(v\) in a three-dimensional vector space \(W\).

Write \(U=\sum_i u_i\), \(U_2=\sum_i u_i^2\), \(V=\sum_i v_i\), \(V_2=\sum_i v_i^2\), and \(D=u^Tv\). The linear matching form gives \(UV=0\). If \(U\ne0\), then \(W\) is the hyperplane \(V=0\). The quadratic matching form on this hyperplane is \((U_2-U^2)V_2+D^2\). Here \(V_2\) has rank three and \(D^2\) has rank at most one; vanishing forces \(U_2=U^2\) and \(D=0\) throughout the hyperplane. Thus \(u\) is a nonzero constant vector, contradicting \(U_2=U^2\).

If \(U=0\), the quadratic matching form on \(W\) is \(U_2(V_2-V^2)+D^2\). When \(U_2=0\), its vanishing gives \(W=u^\perp\), which contains \(u\) and produces a forbidden rank-one direction. When \(U_2\ne0\), the four-dimensional form with matrix \(U_2(I-J)+uu^T\) is nondegenerate: \((I-J)u=u\), and the determinant lemma gives a rank-one update factor of two. Its totally isotropic subspaces have dimension at most two.

The outstanding case is a three-space with a direction of rank at least three that avoids the hook, has trivial simultaneous stabilizer and has no model over a number field of degree at most two.
