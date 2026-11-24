"""Check the five-coordinate Hessian pencil by exact symmetric interpolation."""

from itertools import combinations, permutations, product
from random import Random

import sympy as sp


def elementary(row):
    return [sum(sp.prod(u) for u in combinations(row, k)) for k in range(1, 6)]


def monomial(exponents, values):
    return sp.prod(x**d for d, x in zip(exponents, values))


def pencil(row, t):
    matrix = sp.zeros(5)
    for i, j in combinations(range(5), 2):
        tail = [row[k] for k in range(5) if k not in (i, j)]
        value = sum(tail) + t * sum(u * v for u, v in combinations(tail, 2))
        matrix[i, j] = matrix[j, i] = value
    return matrix


a, b, c, d, e = sym = sp.symbols('a b c d e')
expected = [
    6 * (a*a*c - 4*a*d + 12*e),
    12 * (a*b*c + a*e - 2*b*d),
    6 * (2*a*a*e + a*b*d + a*c*c + b*b*c - 13*b*e - c*d),
    -6 * (a*b*e - a*c*d - b*b*d - b*c*c + 13*c*e - 2*d*d),
    -12 * (2*a*c*e - b*c*d - d*e),
    -6 * (4*a*d*e - b*d*d - 12*e*e),
]
bases = []
for degree in range(5, 11):
    ranges = [range(degree // j + 1) for j in range(1, 6)]
    bases.append([v for v in product(*ranges)
                  if sum(j * k for j, k in enumerate(v, 1)) == degree])

# Full column rank below certifies interpolation in the entire weighted degree.
generator = Random(73682)
points = [[generator.randrange(-4, 7) for _ in range(5)]
          for _ in range(max(map(len, bases)) + 7)]
coordinates = [elementary(row) for row in points]
values = sp.Matrix([[pencil(row, t).det() for t in range(6)] for row in points])
vandermonde = sp.Matrix([[t**i for i in range(6)] for t in range(6)])
coefficients = values * vandermonde.inv().T
for k, basis in enumerate(bases):
    samples = sp.Matrix([[monomial(v, s) for v in basis] for s in coordinates])
    solution, free = samples.gauss_jordan_solve(coefficients[:, k])
    assert free.rows == 0
    recovered = sum(h * monomial(v, sym) for h, v in zip(solution, basis))
    assert sp.expand(recovered - expected[k]) == 0

normalized = sp.groebner([f.subs(a, 1) for f in expected], e, d, c, b, order='lex')
relations = [12*b*b*c - 4*b*c + e, 144*b*b*c - 48*b*c - c + 4*d,
             c*(b-2*c)*(4*b-1), b*c*(4*b-1)**2]
assert all(normalized.reduce(f)[1] == 0 for f in relations)
G = sp.groebner(relations, e, d, c, b, order='lex')
assert all(G.reduce(f.subs(a, 1))[1] == 0 for f in expected)

# Rank-four test for the type with a duplicated value and a third-root triple.
h, k, w, t = sp.symbols('h k w t')
matrix = pencil([h, h, k, k*w, -k*(w+1)], t)
strip = matrix.extract([0, 2, 3, 4], [0, 2, 3, 4])
minor = sp.rem(strip.det(method='domain-ge'), w*w+w+1, w)
factor = 3*(h**3-k**3)*(-h**3*t**2+4*h*h*k**3*t**4-4*h*h*t+
                        4*h*k**3*t**3-4*h+k**3*t**2)
assert sp.expand(minor-factor) == 0

# Check the final trilinear and quartic identities on all pairs of basis vectors.
def matching(*rows):
    return sum(sp.prod(row[j] for row, j in zip(rows, ix))
               for ix in permutations(range(5), len(rows)))


root = [0, 0, 1, w, -1-w]
head = [h, k, 0, 0, 0]
fourier = [[1,0,0,0,0], [0,1,0,0,0], [0,0,1,1,1], root, [0,0,1,-1-w,w]]
for i, x in enumerate(fourier):
    for j, y in enumerate(fourier):
        lx, mx, nx = (int(i == p) for p in (2, 3, 4))
        ly, my, ny = (int(j == p) for p in (2, 3, 4))
        hx, hy = sum(x[:2]), sum(y[:2])
        triple = matching(root, x, y)
        checks = [
            triple - 3*(2*mx*my - (hx+lx)*ny - (hy+ly)*nx),
            matching(root, root, x, y) - 6*(hx*my + hy*mx),
            matching(root, head, x, y) - (h+k)*triple
            - 3*((h*x[0]+k*x[1])*ny + (h*y[0]+k*y[1])*nx),
        ]
        assert all(sp.rem(f.expand(), w*w+w+1, w) == 0 for f in map(sp.sympify, checks))
print('Verified six symmetric coefficients, the normalized ideal, the rank-four minor, and all final bilinear identities.')
