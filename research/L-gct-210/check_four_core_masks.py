"""Exact support classification for MixedSevenKernel.md. Requires SymPy."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations
from math import prod
import sympy as sp

indices = range(4)
orders = tuple(permutations(indices))
triples = tuple(combinations(indices, 3))


def canonical(rows):
    """Permute columns and sort rows; transposition is handled by the caller."""
    return min(tuple(sorted(sum(1 << perm[j] for j in indices if row & (1 << j))
                            for row in rows)) for perm in orders)


def support_orbits():
    orbits = set()
    for rows in combinations_with_replacement(range(1, 16), 4):
        if (rows[0] | rows[1] | rows[2] | rows[3]) != 15:
            continue
        cols = tuple(sum(1 << i for i in indices if rows[i] & (1 << j)) for j in indices)
        orbits.add(min(canonical(rows), canonical(cols)))
    return orbits


def admits_matrix(rows):
    # Row and column scaling normalizes a spanning forest of the support
    # graph to ones. The remaining coordinates range independently over C*.
    parent = list(range(8))
    def root(i):
        while i != parent[i]:
            i = parent[i]
        return i
    matrix = [[0] * 4 for _ in indices]
    variables = []
    for i, row in enumerate(rows):
        for j in indices:
            if not (row & (1 << j)):
                continue
            a, b = root(i), root(4+j)
            if a != b:
                parent[a] = b
                matrix[i][j] = 1
            else:
                x = sp.Symbol("x" + str(len(variables)))
                matrix[i][j] = x
                variables.append(x)
    equations = set()
    for rr in triples:
        for cc in triples:
            q = sum(prod(matrix[i][j] for i, j in zip(rr, p)) for p in permutations(cc))
            if not q:
                continue
            if not variables or len(sp.Poly(q, *variables).terms()) == 1:
                return False
            equations.add(q)
    inv = sp.Symbol("inverse_product")
    equations.add(inv * prod(variables) - 1)
    basis = sp.groebner(sorted(equations, key=sp.default_sort_key), inv, *variables,
                        order="grevlex", domain=sp.QQ)
    return not basis.contains(sp.Integer(1))


orbits = support_orbits()
accepted = {rows for rows in orbits if admits_matrix(rows)}
expected = {(3, 3, 12, 12), (1, 1, 1, 15), (1, 1, 1, 14)}
assert accepted == expected
print("Full-axis support orbits:", len(orbits))
print("Surviving row-mask orbits:", sorted(accepted))

# Independent check of the tangent calculation at a full cross. Summing
# the four outside perturbations gives the pair-incidence Kronecker square.
pairs = tuple(combinations(range(3), 2))
pair_incidence = sp.Matrix([[int(j in p) for j in range(3)] for p in pairs])
cross_derivative = sp.kronecker_product(pair_incidence, pair_incidence)
assert cross_derivative.rank() == 9
print("Rank of the nine normalized cross-tangent equations:", cross_derivative.rank())

# Reconstruct the four top-column coefficient vectors at the cyclotomic slice.
omega = sp.Symbol("omega")
a,b,c,t = sp.symbols("a b c t")
w = sp.symbols("w1:5")
u = sp.Matrix([1, omega, omega**2])
v = sp.Matrix([1, omega**2, omega])
e = sp.ones(3, 1)
matrix = sp.Matrix.hstack(a*u, -a*u, b*v, c*v).col_join(sp.Matrix([w])*t)
calculated = []
for j in indices:
    column = []
    for i in range(3):
        rs = [k for k in indices if k != i]
        cs = [k for k in indices if k != j]
        value = sum(prod(matrix[r,k] for r,k in zip(rs,p)) for p in permutations(cs))
        column.append(sp.expand(value).coeff(t))
    calculated.append(sp.Matrix(column))
expected_columns = [2*b*c*w[1]*u + (a*c*w[2]+a*b*w[3])*e,
                    2*b*c*w[0]*u - (a*c*w[2]+a*b*w[3])*e,
                    a*c*(w[0]-w[1])*e-2*a*a*w[3]*v,
                    a*b*(w[0]-w[1])*e-2*a*a*w[2]*v]
for actual, expected_column in zip(calculated, expected_columns):
    assert all(sp.rem(p, omega**2+omega+1, omega).expand() == 0 for p in actual-expected_column)
print("Cyclotomic slice:", len(calculated)*3, "cofactor coefficients verified")
