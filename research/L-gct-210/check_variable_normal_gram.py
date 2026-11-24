"""Exact rational check of the variable-normal Gram formula and generic example."""
import sympy as sp

eye = sp.eye(5)
ones = sp.ones(5)
cycle = sp.Matrix(5, 5, lambda i, j: int(i == (j+1) % 5))
a = (eye + ones)/6
b = (cycle + ones)/6
forms = []
for i in range(5):
    mask = sp.diag(*[int(j == i) for j in range(5)])
    forms.append(mask*a)
for j in range(5):
    mask = sp.diag(*[int(i == j) for i in range(5)])
    forms.append(b*mask)


def gamma(f, g):
    e = sp.ones(5, 1)
    return (f.T*g).trace() - (
        (f*e).dot(g*e)+(e.T*f).dot(e.T*g))/4 + sp.Rational(3, 50)*sum(f)*sum(g)


gram = sp.Matrix(10, 10, lambda i, j: gamma(forms[i], forms[j]))
coeffs = sp.Matrix.hstack(*[m.reshape(25, 1) for m in forms])
inverse = sp.kronecker_product(eye - ones/4, eye - ones/4)
assert gram == coeffs.T*(inverse - sp.ones(25)/400)*coeffs
assert gram.det() == sp.Rational(116281, 399349999213278658560)
print("Generic example: rank", gram.rank(), "exact determinant", gram.det())

from itertools import combinations
a = sp.Matrix([[sp.Rational(int(j != i),4) for j in range(5)] for i in range(4)] +
              [[sp.Rational(v,8) for v in [3,1,1,1,2]]])
kernel = sp.Matrix([1,-1,-1,-1,2])
assert a.T * kernel == sp.zeros(5, 1)
assert all(sum(row) == 1 and sum(x*x for x in row) == sp.Rational(1,4) for row in a.tolist())
row_gram = a*(sp.Rational(3,50)*ones-eye/4)*a.T
assert a.rank() == row_gram.rank() == 4
third = 0
for weight, row in zip(kernel, a.tolist()):
    u = [x-sp.Rational(1,4) for x in row]
    third += weight**3 * sum(sp.prod(v) for v in combinations(u,3))
assert third == sp.Rational(1,32)
print("Five distinct degenerate row normals: rank", row_gram.rank(), "third-order value", third)
