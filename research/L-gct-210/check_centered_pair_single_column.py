"""Exact column metrics and quadratic operator in CenteredPairSingleColumn.md."""

import itertools

import sympy as sp


unit = sp.ones(4, 1)
column_metric = sp.Matrix([[0, 4, 0, 0], [4, 12, 0, 0],
                           [0, 0, -2, 0], [0, 0, 0, -2]])
# In the 2+2 case z=x*(1,-1,0,0)+y*(0,0,1,-1).
p, q = sp.symbols("p q")
operator = sp.Matrix([[0, 0, p/2, q/2], [0, 0, 0, 0],
                      [0, -p, 0, 0], [0, -q, 0, 0]])
r, n, x, y = sp.symbols("r n x y")
vec = sp.Matrix([n, r, x, y])
assert sp.expand((vec.T*column_metric*operator*vec)[0] - 4*r*(p*x+q*y)) == 0
assert sp.simplify(operator**2*vec - sp.Matrix([-r*(p*p+q*q)/2, 0, 0, 0])) == sp.zeros(4, 1)

# Check the affine four-column derivative, including all second-degree terms.
for j in range(5):
    a = sp.Matrix([2, -3, 4, -3])
    zeroes = sp.Matrix.vstack(unit.T, a.T).nullspace()
    u = (j+1)*zeroes[0]+(2-j)*zeroes[1]
    rvals = [j-2, 3*j+1, 1-4*j]
    zs = [(j+1)*zeroes[0]+zeroes[1], 2*zeroes[0]+(j-2)*zeroes[1]]
    zs.append(-zs[0]-zs[1])
    t = sp.symbols("t")
    rows = [u]+[unit+t*((j+1+rval)*unit+z) for rval, z in zip(rvals, zs)]
    coeff = sp.expand(sum(sp.prod(rows[i][j] for i, j in enumerate(cols))
                          for cols in itertools.permutations(range(4)))).coeff(t, 2)
    expected = sum(2*rval*u.dot(z)-u.dot(z.multiply_elementwise(z))
                   for rval, z in zip(rvals, zs))
    assert sp.simplify(coeff-expected) == 0

# The mean-block inverse length used for the non-singleton branch.
mean = sp.Matrix([[0, 8], [8, -120]])
beta = sp.Matrix([-sp.Rational(2, 3), -5])
assert (beta.T*mean.inv()*beta)[0] == sp.Rational(5, 3)
print("Centered pure-column metric, operator, matching and mean-block checks passed.")
