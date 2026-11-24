"""Exact coefficient checks for the cubic-root common-normal obstruction."""

from itertools import combinations, permutations

import sympy as sp


def elementary(values, degree):
    return sum(sp.prod(choice) for choice in combinations(values, degree))


def permanent(rows):
    return sum(sp.prod(rows[i][j] for i, j in enumerate(order))
               for order in permutations(range(len(rows))))


x = sp.symbols('x:5')
e = [elementary(x, k) for k in range(6)]
gradient = [elementary(x[:i]+x[i+1:], 3) for i in range(5)]
expr = sum(v*v for v in gradient) + 2*e[2]*e[4]+4*e[1]*e[5]
assert sp.rem(expr, e[3], *x) == 0

w, h, t, al, be = sp.symbols('w h t al be')
cyclotomic = w*w+w+1
u = [1, w, w*w]
y = sp.symbols('y:5')
z = sp.symbols('z:5')
Y = [1+t*v for v in y]
Z = [1+t*v for v in z]
p = [al, be, *[h*v for v in u]]

# Each entry is the rectangular matching sum over the two leftover rows.
R = 0
for j, k in combinations(range(5), 2):
    R += sp.prod(p[i] for i in range(5) if i not in (j,k)) * (Y[j]*Z[k]+Y[k]*Z[j])
R = sp.expand(R)
double = R.coeff(al,1).coeff(be,1).coeff(h,1)
single = R.coeff(al,1).coeff(be,0).coeff(h,2)
assert sp.rem(double - permanent([u, Y[2:], Z[2:]]), cyclotomic, w) == 0
linear_u = sum(v*(yi+zi) for v,yi,zi in zip(u,y[2:],z[2:]))
linear_v = sum(v*v*(yi+zi) for v,yi,zi in zip(u,y[2:],z[2:]))
assert sp.rem(double.coeff(t,1)+linear_u, cyclotomic, w) == 0
assert sp.rem(single.coeff(t,1)-linear_v, cyclotomic, w) == 0

J = sp.ones(5)
inv = J/4-sp.eye(5)
k = sp.Matrix([0,0,0,1,1])
assert (k.T*inv*k)[0] == -1
assert (sp.eye(5)/75+6*J/25).rank() == 5
print('Newton identity, both bottom-three coefficients, and inverse Gram checks passed.')
