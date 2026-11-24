"""Exact calculations for restrictions on a candidate for L-gct-210.

The six-dimensional extension test reduces Z[w]/(w^2+w+1) modulo 7
with w mapping to 2. The support test uses rational arithmetic and rank
lower bounds modulo 101. A nonzero minor after either reduction is nonzero
over the complex numbers. Run with Python 3.8 or later.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, factorial, prod

N = 5
P = 7
CELLS = list(product(range(N), repeat=2))
PERMS = list(permutations(range(N)))


def rref(rows, prime=None):
    """Reduce rows and return the pivot columns. Arithmetic is exact."""
    matrix = [[Fraction(x) if prime is None else x % prime for x in row] for row in rows]
    pivots = []
    for col in range(len(matrix[0])):
        active = len(pivots)
        chosen = next((i for i in range(active, len(matrix)) if matrix[i][col]), None)
        if chosen is None:
            continue
        matrix[active], matrix[chosen] = matrix[chosen], matrix[active]
        pivot = matrix[active][col]
        if prime is None:
            row = [x / pivot for x in matrix[active]]
        else:
            row = [x * pow(pivot, -1, prime) % prime for x in matrix[active]]
        matrix[active] = row
        for i, other in enumerate(matrix):
            if i == active or other[col] == 0:
                continue
            multiple = other[col]
            reduced = [x - multiple * y for x, y in zip(other, row)]
            matrix[i] = reduced if prime is None else [x % prime for x in reduced]
        pivots.append(col)
    return matrix[:len(pivots)], pivots


def seed_point(parameters):
    """J plus the six-parameter family of L-gct-180 embedded in five rows."""
    a, b, c, d, e, f = parameters
    w = 2
    rows = [
        [a, -a, b, -b, 0],
        [w*a, -w*a, (-1-w)*b, (1+w)*b, 0],
        [(-1-w)*a, (1+w)*a, w*b, -w*b, 0],
        [c, d, e, f, -c-d-e-f],
        [0]*5,
    ]
    return [(1 + x) % P for row in rows for x in row]


def derivatives(point):
    gradient = [0] * 25
    hessian = [[0] * 25 for _ in range(25)]
    for permutation in PERMS:
        indices = [5*i + permutation[i] for i in range(5)]
        for i, cell in enumerate(indices):
            gradient[cell] += prod(point[indices[k]] for k in range(5) if k != i)
        for i, j in combinations(range(5), 2):
            left, right = indices[i], indices[j]
            value = prod(point[indices[k]] for k in range(5) if k not in (i, j))
            hessian[left][right] += value
            hessian[right][left] += value
    return gradient, hessian


def determinant(matrix, prime=None):
    result = 0
    for order in permutations(range(len(matrix))):
        inversions = sum(a > b for i, a in enumerate(order) for b in order[i+1:])
        result += (-1)**inversions * prod(matrix[i][j] for i, j in enumerate(order))
    return result if prime is None else result % prime


def bilinear(hessian, x, y):
    return sum(x[i] * entry * y[j] for i, row in enumerate(hessian)
               for j, entry in enumerate(row)) % P


def extension_bound():
    """Rule out every eight-dimensional extension of the six original directions.

    The pivot entries (0,0), (0,2), (3,0)..(3,3) are the six parameters.
    Representatives modulo the seed have zeros at these entries. Fifteen
    independent gradients give 15 further homogeneous equations. The resulting
    four-dimensional space contains every such representative.

    The 21 pivot equations lift to independent equations in characteristic zero;
    their pivot minor stays invertible modulo 7. Thus the null basis of these
    equations lifts over the localization as well.

    Two Hessians vanish on any space of extensions. If they shared an isotropic
    plane in dimension four, the determinant of their pencil would be a square
    up to a scalar: in a basis starting with the plane its blocks would be
    [[0, A], [transpose(A), B]]. Its leading coefficient is a unit modulo 7.
    A monic square quartic has a unique monic square root; its two coefficients
    are determined from the top coefficients using division only by 2, so a
    square over C would remain a scalar times a square after reduction. The
    reduced factor 5*t^2+3 has two distinct roots over the algebraic closure.
    """
    gradients = []
    row_choices = [[0] * 4] + [[int(i == j) for i in range(4)] for j in range(4)]
    for a, b, tail in product(range(P), range(P), row_choices):
        gradient, _ = derivatives(seed_point([a, b] + tail))
        if len(rref(gradients + [gradient], P)[1]) > len(gradients):
            gradients.append(gradient)
        if len(gradients) == 15:
            break
    assert len(gradients) == 15
    fixed_entries = (0, 2, 15, 16, 17, 18)
    equations = gradients + [[int(i == j) for j in range(25)] for i in fixed_entries]
    rows, pivots = rref(equations, P)
    assert len(pivots) == 21
    free = [j for j in range(25) if j not in pivots]
    basis = []
    for j in free:
        vector = [int(k == j) for k in range(25)]
        for row, k in zip(rows, pivots):
            vector[k] = -row[j] % P
        basis.append(vector)
    hessians = []
    for parameters in ([0]*6, [0, 0, 1, 0, 0, 0]):
        _, hessian = derivatives(seed_point(parameters))
        hessians.append([[bilinear(hessian, x, y) for y in basis] for x in basis])
    h0, h1 = hessians
    values = [determinant([[h1[i][j] + t*h0[i][j] for j in range(4)]
                           for i in range(4)], P) for t in range(P)]
    # Degree at most four; seven evaluations uniquely determine the polynomial.
    assert values == [(1+t)**2 * (5*t*t+3) % P for t in range(P)]
    assert determinant(h0, P) == 5
    print("6D seed: 15 independent gradients, quotient ambient dimension 4")
    print("det(H1 + t H0) mod 7 = (t+1)^2 (5t^2+3); upper bound for extensions: 7")



def sum_zero_gram(cells):
    """Second derivative divided by 3!, in the basis e_x - e_last."""
    origin = cells[-1]

    def pair(x, y):
        return int(x[0] != y[0] and x[1] != y[1])

    return [[pair(x, y) - pair(x, origin) - pair(origin, y)
             for y in cells[:-1]] for x in cells[:-1]]


def sparse_supports():
    """Rule out at most 18 varying entries for every putative 9-dimensional space.

    RowBound.lean proves that each row and each column must have rank >= 2.
    For each remaining mask the second derivative gives a Witt-index bound.
    In the four borderline masks a 9-plane would have to contain the radical
    of the second derivative on the sum-zero hyperplane.
    """
    bound_prime = 101
    relabel = [[sum(1 << perm[j] for j in range(5) if mask & (1 << j))
                for mask in range(32)] for perm in PERMS]
    seen = set()
    covered = 0
    orbits = 0
    border_cases = []
    for masks in combinations_with_replacement(range(32), 5):
        size = sum(bin(row).count("1") for row in masks)
        if size > 18 or masks in seen:
            continue
        orbit = {tuple(sorted(action[row] for row in masks)) for action in relabel}
        seen.update(orbit)
        orbits += 1
        row_orders = 120 // prod(factorial(k) for k in Counter(masks).values())
        covered += row_orders * len(orbit)
        if size < 10:
            continue
        row_sizes = [bin(row).count("1") for row in masks]
        column_sizes = [sum((row >> j) & 1 for row in masks) for j in range(5)]
        if min(row_sizes + column_sizes) < 2:
            continue
        cells = [(i, j) for i, j in CELLS if masks[i] & (1 << j)]
        gram = sum_zero_gram(cells)
        _, pivots = rref(gram, bound_prime)
        # Reduction can only lower rank, hence only increase this upper bound.
        if size - 1 - (len(pivots) + 1) // 2 >= 9:
            border_cases.append((masks, cells, gram))
    assert covered == sum(comb(25, k) for k in range(19))
    expected = {(3, 13, 29, 29, 31), (3, 28, 28, 31, 31),
                (3, 29, 29, 29, 30), (7, 7, 27, 27, 27)}
    assert {rows for rows, _, _ in border_cases} == expected
    print(f"Supports of size at most 18: {covered} labelled masks, {orbits} orbits")
    for masks, cells, gram in border_cases:
        reduced, pivots = rref(gram)
        assert len(cells) == 18 and len(pivots) == 16
        # A totally isotropic 9-plane in this 17-dimensional space of rank 16
        # contains its one-dimensional radical (the quotient has Witt index 8).
        free, = [i for i in range(17) if i not in pivots]
        coeff = [Fraction(int(i == free)) for i in range(17)]
        for row, pivot in zip(reduced, pivots):
            coeff[pivot] = -row[free]
        coeff.append(-sum(coeff))
        direction = [Fraction(0)] * 25
        for (i, j), x in zip(cells, coeff):
            direction[5*i+j] = x
        point = [1+x for x in direction]
        value = sum(prod(point[5*i+j] for i, j in enumerate(p)) for p in PERMS)
        if value != 120:
            print(f"  {masks}: permanent at radical translate = {value}")
            continue
        # For the other masks the radical vector has integral entries.
        assert all(x.denominator == 1 for x in direction)
        indices = [5*i+j for i, j in cells]
        g0, h0 = derivatives([1]*25)
        g1, _ = derivatives([int(x) for x in point])
        gradients = [[g[i] for i in indices] for g in (g0, g1)]
        blocks = [[h0[i][j] for j in indices] + [g[k] for g in gradients]
                  for k, i in enumerate(indices)]
        blocks += [g + [0, 0] for g in gradients]
        _, piv = rref(blocks, bound_prime)
        # L x C^2 is isotropic for this block matrix: both gradients kill L,
        # and the Hessian vanishes on L x L. Rank 19 in dimension 20 permits
        # an isotropic subspace of dimension at most 10. Thus dim L <= 8.
        assert len(piv) == 19
        print(f"  {masks}: bordered Hessian rank >= 19; dimension <= 8")
    print("Every 9-dimensional counterexample must vary in at least 19 entries.")


def cyclic_row_pairing():
    """Verify the two scalars used in the Fourier proof for cyclically stable L.

    In weight a, the rows are w^(a*i) times a single row vector. The weight-0
    part is zero since 120 times the product of its five shifted entries must
    remain 120. Each other weight space has a common zero column: the top
    coefficient is 120 times the product of the five row-vector entries.
    Opposite weights have pairing -30 times J-I. Deleting their two respective
    zero coordinates leaves an invertible 4x4 pairing, so their dimensions sum
    to at most 4. The pairs (1,4) and (2,3) give total dimension at most 8.
    """
    for a in range(1, 5):
        counts = Counter(a*(i-k) % 5 for i, k in CELLS if i != k)
        # For a primitive fifth root, 1+w+w^2+w^3+w^4 = 0.
        assert [counts[j] for j in range(5)] == [0, 5, 5, 5, 5]
    minors = []
    for a, b in CELLS:
        minor = [[int(i != j) for j in range(5) if j != b]
                 for i in range(5) if i != a]
        minors.append(abs(determinant(minor)))
    assert Counter(minors) == {1: 20, 3: 5}
    print("Cyclic row case: mixed coefficient -30; all 25 pairing minors nonzero.")


if __name__ == "__main__":
    extension_bound()
    sparse_supports()
    cyclic_row_pairing()
