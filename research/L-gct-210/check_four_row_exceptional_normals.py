"""Exact verification of the fixed marginal Gram and the centered null normal."""

from itertools import combinations, permutations

import sympy as sp


v = sp.symbols('u:3')
gram = sp.Matrix(3, 3, lambda i, j: 8*v[i]**2-9 if i == j else 3-4*v[i]*v[j])
pairs = list(combinations(range(3), 2))
minors = [gram.extract(a, b).det() for a in pairs for b in pairs]
u, v1, v2 = v
simple = [u*u-u*v2+v2*v2-1, u*v1-u*v2-v1*v2+2*v2*v2-1,
          (u-v1)*(v2-1)*(v2+1), v1*v1-v1*v2+v2*v2-1, v2*(v2-1)*(v2+1)]
for generators, targets in [(minors, simple), (simple, minors)]:
    gb = sp.groebner(generators, *v, order='lex')
    assert all(gb.reduce(f)[1] == 0 for f in targets)

h, x, y, z = sp.symbols('h x y z')
tail = x, y, z
physical = h, x, y, z
weights = 2, 1, 1, 1
t = sp.Symbol('t')


def specialize(expression):
    symmetric, remainder, change = sp.symmetrize(sp.expand(expression), tail, formal=True)
    assert remainder == 0
    return sp.factor(symmetric.subs({change[0][0]: -2*h, change[1][0]: 3*h*h, change[2][0]: t}))


quartic = h*h*(x*y+x*z+y*z)+2*h*x*y*z
assert specialize(sp.hessian(quartic, physical).det()) == -48*h*h*t*t
matrix = sp.Matrix([[m*n**degree for m, n in zip(weights, physical)] for degree in (0,1,2)])
r = [(-1)**i*matrix[:, [j for j in range(4) if i != j]].det() for i in range(4)]
assert specialize(sum(m*n*b**2 for m,n,b in zip(weights,physical,r))) == -150*h*t*(4*h**3+t)
assert specialize(sum(m*b**2 for m,b in zip(weights,r))) == -90*(4*h**3+t)**2


def matching(*rows):
    return sum(sp.prod(row[j] for row, j in zip(rows, order))
               for order in permutations(range(5), len(rows)))


sqrt2i = sp.sqrt(-2)
n4 = sp.Matrix([1, 1, -1+sqrt2i, -1-sqrt2i, 0])
H4 = sp.hessian(quartic, physical).subs(dict(zip(physical, [n4[0], *n4[2:]]))).applyfunc(sp.simplify)
assert H4.rank() == 3
assert (H4*sp.Matrix([-1, -1, -1, 1])).applyfunc(sp.simplify) == sp.zeros(4, 1)
e5 = sp.eye(5)[:, 4]
e = sp.ones(5, 1)
for v in sp.eye(5).columnspace():
    value = matching(n4, n4, e5-e/5, v)
    assert sp.simplify(value-sp.Rational(6,5)*n4.applyfunc(lambda s: s*s).dot(v)) == 0

omega = (-1+sp.sqrt(-3))/2
n3 = sp.Matrix([0,0,1,omega,-1-omega])
fourier = [sp.Matrix([1,1,0,0,0]), sp.Matrix([0,0,1,1,1]), n3, n3.applyfunc(lambda s:s*s)]
for i,v in enumerate(fourier):
    for j,w in enumerate(fourier):
        expected = 12*(int(i==0 and j==2)+int(i==2 and j==0))
        assert sp.simplify(matching(n3,n3,v,w)-expected) == 0
print('Verified the Gram ideal, weighted Hessians, Vandermonde identities, and both exceptional normals.')
