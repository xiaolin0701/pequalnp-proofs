"""Exact arithmetic checks for OppositeRowDegenerateNormal.md (SymPy)."""

from itertools import combinations
import sympy as sp


def elementary(values, degree):
    return sum(sp.prod(choice) for choice in combinations(values, degree))


a, b, c, omega, lam, x = sp.symbols("a b c omega lam x")
ones = sp.ones(5, 1)
base = sp.ones(5) - sp.eye(5)
normal = sp.Matrix([a, b, c, 1, 1])
c_normal = sp.Matrix(5, 5, lambda i, j: 0 if i == j else 1 - normal[i] - normal[j])
assert (c_normal * ones - 3 * (ones - normal)).subs(c, -1-a-b).applyfunc(sp.expand).is_zero_matrix
det, remainder, generators = sp.symmetrize(c_normal.det(), [a, b, c], formal=True)
s1, s2, s3 = (pair[0] for pair in generators)
assert remainder == 0
assert sp.expand(det.subs({s1: -1, s2: 1}) - 6 * (5 * s3 - 3)) == 0


def matching_matrix(left, right):
    def entry(i, j):
        if i == j:
            return 0
        used = {i, j}
        return sum(
            left[k] * right[m]
            for k in range(5) if k not in used
            for m in range(5) if m not in used and k != m
        )
    return sp.Matrix(5, 5, entry)


def reduce_units(value):
    return sp.expand(sp.rem(sp.rem(sp.expand(value), omega**2 + omega + 1, omega),
                            2 * lam**2 + 1, lam))


w = sp.Matrix([0, omega, -1 - omega, 1, 1])
delta = sp.Matrix([0, 0, 0, 1, -1])
g = sp.Matrix([1 + w[i] if i < 3 else 0 for i in range(5)])
first = base.inv() * matching_matrix(w, delta)
eigenvector = base.inv() * g + lam * delta
assert (first * eigenvector - 2 * lam * eigenvector).applyfunc(reduce_units).is_zero_matrix
second = base.inv() * matching_matrix(w, sp.eye(5)[:, 3])
image = (second * eigenvector).applyfunc(reduce_units)
assert reduce_units(elementary(image, 3) - (sp.Rational(1, 4) - 9 * lam / 8)) == 0

poly = x**3 + x**2 + x - sp.Rational(3, 5)
assert sp.discriminant(poly, x) == -sp.Rational(528, 25)
assert poly.subs(x, -sp.Rational(1, 3)) == -sp.Rational(116, 135)
half = sp.Rational(1, 2)
assert -sp.diff(poly, x).subs(x, half) / (2 * poly.subs(x, half)) == -5
h = 3 + 5 * sp.invert(2 * x - 1, poly, x)
assert sp.expand(11 * h + 100 * x**2 + 150 * x + 142) == 0
squares = sum((value**2 - value)**2 for value in (a, b, c))
norm, remainder, _ = sp.symmetrize(squares, [a, b, c], formal=True)
assert remainder == 0
assert norm.subs({s1: -1, s2: 1, s3: sp.Rational(3, 5)}) == -12

print("Degenerate opposite-row arithmetic checks passed.")
