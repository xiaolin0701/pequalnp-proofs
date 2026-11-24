"""Certify the first six coordinate hyperplanes of the seven-parameter level family."""
from collections import defaultdict
from itertools import combinations_with_replacement, permutations
from math import prod
from random import Random

PRIME = 13
OMEGA = 3
SEED_PIVOTS = (0, 2, 15, 16, 17, 18, 4)
MATCHINGS = tuple(tuple(5*i+j for i, j in enumerate(order)) for order in permutations(range(5)))


def seed(q):
    a, b, c, d, e, f, h = q
    w = OMEGA
    return [a, -a, b, -b, h, w*a, -w*a, (-1-w)*b, (1+w)*b, h,
            (-1-w)*a, (1+w)*a, w*b, -w*b, h, c, d, e, f, -(c+d+e+f), 0, 0, 0, 0, -3*h]


def gradient(matrix):
    values = [0]*25
    for match in MATCHINGS:
        for index in match:
            values[index] += prod(matrix[j] for j in match if j != index)
    return [v % PRIME for v in values]


def row_basis(rows):
    """Compute a reduced row basis; each new pivot has value one."""
    basis = {}
    for row in rows:
        r = [v % PRIME for v in row]
        for pivot in sorted(basis):
            if r[pivot]:
                coeff = r[pivot]
                r = [(x-coeff*y) % PRIME for x, y in zip(r, basis[pivot])]
        pivot = next((i for i, x in enumerate(r) if x), None)
        if pivot is None:
            continue
        scale = pow(r[pivot], -1, PRIME)
        r = [(x*scale) % PRIME for x in r]
        for old, b in basis.items():
            if b[pivot]:
                coeff = b[pivot]
                basis[old] = [(x-coeff*y) % PRIME for x, y in zip(b, r)]
        basis[pivot] = r
    return basis


def nullspace(rows):
    basis = row_basis(rows)
    return [[(-basis[k][j]) % PRIME if k in basis else int(k == j) for k in range(25)]
            for j in range(25) if j not in basis]


def homogeneous_forms(point, directions):
    """The degree 2 through 5 components of per(point + sum x_j direction_j)."""
    total = defaultdict(int)
    for match in MATCHINGS:
        pol = {(): 1}
        for index in match:
            terms = [((), point[index])]
            terms.extend(((j,), v[index]) for j, v in enumerate(directions) if v[index])
            new = defaultdict(int)
            for mon, coeff in pol.items():
                for m, scalar in terms:
                    new[tuple(sorted(mon+m))] += coeff*scalar
            pol = new
        for mon, coeff in pol.items():
            total[mon] += coeff
    return [{mon: coeff % PRIME for mon, coeff in total.items() if len(mon) == deg and coeff % PRIME}
            for deg in range(2, 6)]


def macaulay_quotient(forms, n, d):
    monomials = list(combinations_with_replacement(range(n), d))
    indices = {m: i for i, m in enumerate(monomials)}
    def rows():
        for form in forms:
            if not form:
                continue
            deg = len(next(iter(form)))
            if deg > d:
                continue
            for multiplier in combinations_with_replacement(range(n), d-deg):
                row = [0]*len(monomials)
                for m, c in form.items():
                    row[indices[tuple(sorted(m+multiplier))]] = c
                yield row
    rank = len(row_basis(rows()))
    return len(monomials), rank, len(monomials)-rank


def check(drop):
    rng = Random(131)
    points = [[0]*7] + [[rng.randrange(PRIME) if j != drop else 0 for j in range(7)] for _ in range(50)]
    matrices = [[1+x for x in seed(q)] for q in points]
    equations = [gradient(v) for v in matrices]
    equations.extend([int(i == k) for k in range(25)] for j, i in enumerate(SEED_PIVOTS) if j != drop)
    directions = nullspace(equations)
    forms = [f for matrix in matrices[:8] for f in homogeneous_forms(matrix, directions)]
    d = 6 if len(directions) == 4 else 2
    total, rank, quotient = macaulay_quotient(forms, len(directions), d)
    print(f'drop {drop}: residual {len(directions)}, degree {d}, monomials {total}, rank {rank}, quotient {quotient}')
    assert quotient < d+1


if __name__ == '__main__':
    assert (OMEGA**2+OMEGA+1) % PRIME == 0
    for i in range(6):
        check(i)
