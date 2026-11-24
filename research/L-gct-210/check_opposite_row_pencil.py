"""Finite-field determinant certificate for the exceptional opposite-row normal."""

from itertools import combinations, permutations
from math import prod


P = 29
W = [16, 19, 22, 1, 1]


def kernel_basis(rows):
    mat = [[x % P for x in row] for row in rows]
    pivots = []
    for j in range(len(mat[0])):
        i = len(pivots)
        pivot_row = next((k for k in range(i, len(mat)) if mat[k][j]), None)
        if pivot_row is None:
            continue
        mat[i], mat[pivot_row] = mat[pivot_row], mat[i]
        inv = pow(mat[i][j], -1, P)
        mat[i] = [x * inv % P for x in mat[i]]
        for k, row in enumerate(mat):
            if k != i:
                mat[k] = [(x - row[j] * y) % P for x, y in zip(row, mat[i])]
        pivots.append(j)
    basis = []
    for free in range(len(mat[0])):
        if free not in pivots:
            vector = [int(j == free) for j in range(len(mat[0]))]
            for i, j in enumerate(pivots):
                vector[j] = -mat[i][free] % P
            basis.append(vector)
    return basis


def ambient_hessian(t):
    # The 20 variables give rows u,-u,Z1,Z2,Z3 in row-major order.
    base = [[1 + t * w for w in W], [1 - t * w for w in W]] + [[1] * 5] * 3
    mat = [[0] * 20 for _ in range(20)]
    for perm in permutations(range(5)):
        for i, j in combinations(range(5), 2):
            a = 5 * max(0, i - 1) + perm[i]
            b = 5 * max(0, j - 1) + perm[j]
            value = prod(base[k][perm[k]] for k in range(5) if k != i and k != j)
            if i == 1 or j == 1:
                value = -value
            mat[a][b] += value
            mat[b][a] += value
    return mat


def restrict(mat, basis):
    images = [[sum(a * b for a, b in zip(row, x)) % P for row in mat] for x in basis]
    return [[sum(a * b for a, b in zip(x, y)) % P for y in images] for x in basis]


def determinant(mat):
    mat = [row[:] for row in mat]
    result = 1
    for i in range(len(mat)):
        k = next((k for k in range(i, len(mat)) if mat[k][i] % P), None)
        if k is None:
            return 0
        if k != i:
            mat[i], mat[k] = mat[k], mat[i]
            result = -result
        pivot = mat[i][i] % P
        result = result * pivot % P
        for k in range(i + 1, len(mat)):
            factor = mat[k][i] * pow(pivot, -1, P) % P
            mat[k] = [(a - factor * b) % P for a, b in zip(mat[k], mat[i])]
    return result


def main():
    assert all((5 * (t**3 + t**2 + t) - 3) % P == 0 for t in W[:3])
    g = [w * (w - 1) % P for w in W]
    equations = [
        [0] * 5 + [1] * 15, [1 - w for w in W] + [0] * 15,
        [0] * 5 + 3 * g, [0, 0, 0, 1, 0] + [0] * 15,
    ]
    basis = kernel_basis(equations)
    assert len(basis) == 16
    h0, hp, hm = [restrict(ambient_hessian(t), basis) for t in (0, 1, -1)]
    h1 = [[(a - b) * pow(2, -1, P) % P for a, b in zip(ra, rb)]
          for ra, rb in zip(hp, hm)]
    values = []
    for x in range(17):
        mat = [[a + x * b for a, b in zip(ra, rb)] for ra, rb in zip(h0, h1)]
        value = determinant(mat)
        assert value == -8 * (x*x + 3) * (x*x - 8) % P
        values.append(value)
    print("det(H0 + x H1) = -8 (x² + 3)(x² - 8) over F_29")
    print("values at x=0,...,16:", *values)


if __name__ == "__main__":
    main()
