"""Exact arithmetic for the inverse Gram and two-column identities."""

from itertools import combinations

import sympy as sp


e = sp.ones(5, 1)
core = sp.Matrix.hstack(sp.Matrix([1, 1, 1, 0, 0]), sp.eye(5)[:, 3], sp.eye(5)[:, 4])
hessian = sp.kronecker_product(sp.ones(4) - sp.eye(4), sp.ones(5) - sp.eye(5))
centroid = sp.ones(20, 1)
omega = (-1 + sp.sqrt(-3)) / 2
choices = [
    (sp.Matrix([1, -1, 0, 0, 0]), sp.Matrix([1, -1, 0, 0, 0])),
    (sp.Matrix([1, omega, -1-omega, 0, 0]), sp.Matrix([1, -1-omega, omega, 0, 0])),
]
for first, second in choices:
    basis = sp.Matrix.hstack(
        sp.diag(core, core, core, core),
        sp.kronecker_product(sp.eye(4)[:, 0], first),
        sp.kronecker_product(sp.eye(4)[:, 1], second),
    )
    gram = (basis.T * hessian * basis).applyfunc(sp.simplify)
    dual = gram.inv()
    total = basis.T * centroid
    assert (total.T * dual * total)[0] == sp.Rational(5, 3)
    tangent = dual - dual * total * total.T * dual / sp.Rational(5, 3)
    low = basis.T * sp.kronecker_product(sp.eye(4)[:, 2], core[:, 0]/3)
    high = basis.T * sp.kronecker_product(sp.eye(4)[:, 1], core[:, 0]/3)
    high = high + sp.Symbol('contrast')*sp.eye(14)[:, -1]
    normals = sp.Matrix.hstack(low, high)
    assert normals.T * tangent * normals == sp.Matrix([[37, -23], [-23, 37]])/720

pairs = list(combinations(range(5), 2))
disjoint = sp.Matrix([[int(set(i).isdisjoint(j)) for j in pairs] for i in pairs])
assert disjoint**2 == 2*sp.eye(10) - disjoint + sp.ones(10)
assert disjoint.det() == 48

# The rank-one normal of the two-dimensional first-row normal space.
Q = sp.eye(5) - sp.Rational(41, 160)*e*e.T
assert Q.inv() == sp.eye(5) - sp.Rational(41, 45)*e*e.T
u = sp.Matrix(sp.symbols('u:5'))
s = sum(u)
r = u - sp.Rational(41, 45)*s*e
block = r - sum(r)*e/4
for i in range(4):
    coefficient = sp.Integer(int(i == 0)) - sp.Rational(1, 3)
    apparent = 3 * (coefficient*block - sum(r)*e/240)
    expected = 2*u if i == 0 else -u + s*e/15
    assert (apparent-expected).applyfunc(sp.expand) == sp.zeros(5, 1)
g = -u + s*e/15
assert sp.expand(g.dot(g)-sp.Rational(9, 5)*sum(g)**2) == sp.expand(u.dot(u)-sp.Rational(41, 45)*s**2)

# The cubic on the three-dimensional nullspace if three rows lie in T.
a, b, t = sp.symbols('a b t')
c = [a, b, -a-b, t]
e3 = sum(sp.prod(v) for v in combinations(c, 3))
assert sp.expand(e3 + a*b*(a+b) + t*(a*a+a*b+b*b)) == 0
assert sp.gcd(a*b*(a+b), a*a+a*b+b*b) == 1
print('Verified both contrast models, the 2-subset inverse, the forced row direction, and the root cubic.')
