"""A complex level space with all row and column sums zero has dimension <= 7.

Let E be the 16-dimensional space of doubly centered 5 x 5 matrices, with
the nondegenerate bilinear dot product. The projection P onto E subtracts
each row and column mean and adds the grand mean. The polarized quadratic
and cubic homogeneous permanent coefficients on E are nonzero multiples
of sum(x_i y_i) and sum(x_i y_i z_i). For the cubic, use inclusion-
exclusion for the two sets of three distinct indices: any singleton
block of either index partition sums to zero, and the single three-block
has Möbius coefficient 2. Both index partitions thus contribute 2.

A putative eight-plane K equals its own orthogonal complement in E.
The cubic identity then makes K closed under P(x*y), with entrywise
multiplication. It therefore contains a nonzero x with P(x*x)=lambda*x:
either some nonzero x squares to zero or the quadrics P(x*x)=t*x in
projective space on K plus one coordinate have no points at t=0. In
the latter case their projective intersection is finite (it is contained
in an affine chart), and Bézout gives length 2^dim(K). The point x=0,
t=1 is simple, leaving a nonzero solution. In either case sum(x_i^2)=0.

All eigenvalue and norm equations are rational. A complex solution on
any normalized nonzero-coordinate chart gives one over the algebraic
numbers by the Nullstellensatz. Embed its number field in the algebraic
closure of Q_2. Scale x and lambda so all entries of x are integral,
with at least one unit. The equation implies lambda is integral. Modulo
the maximal ideal, x*x is already doubly centered by Frobenius, hence
P(x*x)=x*x. The primitive vector makes lambda a unit, so normalize
lambda=1. Every residue entry now equals 0 or 1, even over the algebraic
closure of the residue field. The 16 independent entries give all cases.

Each binary residue has at most one fixed-point lift of x -> P(x*x):
if the difference has valuation t>0, then its image has valuation at
least min(1+t,2t). Iterating therefore converges to the same lift even
over ramified extensions. Starting from the integer matrix of zeros and
ones, each iteration gives at least one more correct binary digit.
Below, every nonzero residue has nonzero squared norm already mod 64.
This contradicts the necessary isotropy of the eigenvector.

Consequently a general nine-plane must realize at least two independent
patterns of row and column sums, by applying rank-nullity to the sum map.
There is also a nine-dimensional bound if just the row sums vanish.
In that case the ambient space is C^5 tensor H, with H the centered
column factor, and its quadratic form is (I-J) tensor dot. In dimension
10 the space would be self-dual. A normalized covector b for any column
j annihilates it (otherwise that column can be set to zero in J+L).
Its inverse under the form is the rank-one vector u tensor v, where
u=b-1/4 and v=e_j-1/5. For a rank-one direction the kth permanent
coefficient is k!(5-k)! e_k(u)e_k(v). The four values e_2(v)..e_5(v)
are nonzero and sum(u)=-1/4. Thus u has only one nonzero coordinate:
its coordinates are roots of t^4(t+1/4). We have a pure row direction
with row vector v for each j. Directions for different columns must
belong to the same row: for different row indices their mixed quadratic
pairing is proportional to v_j dot v_k=-1/5. These five vectors span a
full centered row, where the bound in FullRow.lean is eight. This rules
out dimension ten. Transposition exchanges rows and columns.

Run with Python 3.8+. All calculations are integer arithmetic.
"""

from collections import Counter

MODULUS = 64
INV_FIVE = pow(5, -1, MODULUS)


def from_bits(bits):
    matrix = [[0]*5 for _ in range(5)]
    for i in range(4):
        for j in range(4):
            a = bits >> (4*i+j) & 1
            matrix[i][j] = a
            matrix[4][j] ^= a
            matrix[i][4] ^= a
            matrix[4][4] ^= a
    return matrix


def centered_square(x):
    squared = [[v*v for v in row] for row in x]
    row_means = [sum(row)*INV_FIVE for row in squared]
    col_means = [sum(col)*INV_FIVE for col in zip(*squared)]
    grand_mean = sum(row_means)*INV_FIVE
    return [[(v - row_means[i] - col_means[j] + grand_mean) % MODULUS
             for j,v in enumerate(row)] for i,row in enumerate(squared)]


def main():
    excluded = Counter()
    for bits in range(1, 1 << 16):
        matrix = from_bits(bits)
        for precision in (4, 8, 16, 32, 64):
            matrix = centered_square(matrix)
            if sum(v*v for row in matrix for v in row) % precision:
                excluded[precision] += 1
                break
        else:
            raise AssertionError(f"Unresolved residue {bits}")
    assert excluded == {4:32640, 8:20920, 16:2950, 32:3625, 64:5400}
    print("Nonzero residues excluded by modulus:", sorted(excluded.items()))
    print("Every doubly centered complex level space has dimension at most seven.")


if __name__ == "__main__":
    main()
