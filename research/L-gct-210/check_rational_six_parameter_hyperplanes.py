"""Exclude all rational hyperplanes of the seven-parameter seed after split reduction at 13."""
from collections import Counter
from functools import lru_cache
from itertools import product
from random import Random

import check_six_parameter_hyperplanes as seed_test

P = seed_test.PRIME


def projective(n):
    for first in range(n):
        for tail in product(range(P), repeat=n-1-first):
            yield (0,)*first + (1,) + tail


def kernel(rows, n):
    basis = seed_test.row_basis(rows)
    return [[(-basis[k][j]) % P if k in basis else int(k == j) for k in range(n)]
            for j in range(n) if j not in basis]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b)) % P


def linear_combination(x, basis):
    return [dot(x, column) for column in zip(*basis)]


def solutions(matrix, target):
    n = len(matrix[0])
    basis = seed_test.row_basis([row+[b] for row, b in zip(matrix, target)])
    if n in basis:
        return
    particular = [basis[j][-1] if j in basis else 0 for j in range(n)]
    homogeneous = kernel(matrix, n)
    if not homogeneous:
        yield particular
        return
    for x in product(range(P), repeat=len(homogeneous)):
        direction = linear_combination(x, homogeneous)
        yield [(u+v) % P for u, v in zip(particular, direction)]


@lru_cache(maxsize=None)
def gradient_affine_coefficients(t):
    """Gradient values at q=0 and differences at the four axes of the fourth row."""
    a, b, h = t
    gradients = []
    for j in range(5):
        params = [a, b, 0, 0, 0, 0, h]
        if j:
            params[j+1] = 1
        gradients.append(seed_test.gradient([1+x for x in seed_test.seed(params)]))
    return [gradients[0]] + [[(x-y) % P for x, y in zip(row, gradients[0])] for row in gradients[1:]]


def mixed_exceptional_normals():
    rng = Random(177)
    points = [tuple(rng.randrange(P) for _ in range(3)) for _ in range(22)]
    samples = [(t, gradient_affine_coefficients(t)) for t in points]
    active = sorted(seed_test.row_basis(row for _, block in samples for row in block))
    n = len(active)
    assert n == 17  # Eight-dimensional sample kernel includes the original seven-plane.
    blocks = [(t, [[row[j] for j in active] for row in block]) for t, block in samples]
    all_linear = [row for _, block in blocks for row in block[1:]]
    constant_only = kernel(all_linear, n)
    assert len(constant_only) == 1
    z0 = constant_only[0]
    pivot = next(i for i, x in enumerate(z0) if x)
    normals = set()
    fiber_counts = Counter()
    for v in projective(4):
        a = next(k for k, x in enumerate(v) if x)
        equations = [[(x-v[b]*y) % P for x, y in zip(block[b+1], block[a+1])]
                     for _, block in blocks for b in range(4) if b != a]
        equations.append([int(i == pivot) for i in range(n)])  # choose complement to z0
        allowed = kernel(equations, n)
        if not allowed:
            continue
        fiber_counts[len(allowed)] += 1
        for coeffs in projective(len(allowed)):
            y = linear_combination(coeffs, allowed)
            matrix, values = [], []
            for t, block in blocks:
                beta = dot(block[a+1], y)
                matrix.append([beta*x % P for x in t]+[dot(block[0], z0)])
                values.append(dot(block[0], y))
            for na, nb, nh, _ in solutions(matrix, values):
                normals.add((na, nb, *v, nh))
    assert fiber_counts == {1: 2, 2: 16}
    assert len(normals) == 18
    return normals


def pure_exceptional_normals():
    rng = Random(131)
    pairs = [(rng.randrange(P), rng.randrange(P)) for _ in range(16)]
    exceptionals = set()
    for ell in projective(3):
        pivot = next(i for i, v in enumerate(ell) if v)
        others = [i for i in range(3) if i != pivot]
        rows = []
        for u, v in pairs:
            t = [0]*3
            t[others[0]], t[others[1]] = u, v
            t[pivot] = -dot(t, ell) % P  # the leading coefficient is one
            rows.extend(gradient_affine_coefficients(tuple(t)))
        # Subtract retained seed basis vectors, choosing the omitted coordinate as free.
        seed_pivot = (0, 1, 6)[pivot]
        rows.extend([int(k == i) for k in range(25)] for j, i in enumerate(seed_test.SEED_PIVOTS)
                    if j != seed_pivot)
        residual = len(kernel(rows, 25))
        if residual > 2:
            exceptionals.add((ell[0], ell[1], 0, 0, 0, 0, ell[2]))
    assert len(exceptionals) == 3
    return exceptionals


def check_hyperplane(ell):
    pivot = next(i for i, v in enumerate(ell) if v)
    rng = Random(131)
    points = []
    for _ in range(51):
        q = [rng.randrange(P) for _ in ell]
        q[pivot] = 0
        q[pivot] = -dot(ell, q)*pow(ell[pivot], -1, P) % P
        points.append([1+x for x in seed_test.seed(q)])
    rows = [seed_test.gradient(m) for m in points]
    rows.extend([int(i == k) for k in range(25)] for j, i in enumerate(seed_test.SEED_PIVOTS) if j != pivot)
    directions = kernel(rows, 25)
    forms = [f for point in points[:10] for f in seed_test.homogeneous_forms(point, directions)]
    count, rank, quotient = seed_test.macaulay_quotient(forms, len(directions), 6)
    assert quotient < 7, (ell, count, rank)
    return quotient


if __name__ == '__main__':
    # A known coordinate hyperplane rules out every 8-plane containing the full seed in characteristic 13.
    seed_test.check(2)
    mixed = mixed_exceptional_normals()
    pure = pure_exceptional_normals()
    values = Counter(check_hyperplane(ell) for ell in sorted(mixed | pure))
    print(f'{(P**7-1)//(P-1)} rational hyperplanes, {len(mixed)} mixed and {len(pure)} pure exceptions')
    print('Degree-six quotient dimensions among exceptions:', dict(sorted(values.items())))
