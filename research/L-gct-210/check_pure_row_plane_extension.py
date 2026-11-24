"""Exact coefficient checks for PureRowPlaneExtension.md, using SymPy."""
from itertools import permutations
from math import prod
from sympy import Rational, expand, symbols

n = range(5)
b1,b2,c1,c2 = symbols("b1 b2 c1 c2")
w3,w4 = symbols("w3 w4")
w = (0, 0, w3, w4, -w3-w4)
B, C = b1+b2, c1+c2
f = symbols("f1:6")
g = symbols("g1:6")
u = symbols("u1:6")
zero = (0,)*5
W = (zero, zero, w, zero, zero)
T = ((b1,b2,0,0,0),(c1,c2,0,0,0),symbols("d1:6"),zero,zero)
Y = (f,g,symbols("h1:6"),u,zero)


def mixed(directions):
    coeff = 0
    for p in permutations(n):
        for distinct_rows in permutations(n, len(directions)):
            coeff += prod(D[i][p[i]] for D, i in zip(directions, distinct_rows))
    return expand(coeff)


quadratic = mixed((W, Y))
cubic = mixed((T, W, Y))
assert expand(quadratic+6*sum(w[j]*(f[j]+g[j]+u[j]) for j in n)) == 0
assert expand(cubic+2*sum(w[j]*(C*f[j]+B*g[j]+(B+C)*u[j]) for j in n)) == 0

a, b, P, Q, v, z = symbols("alpha beta P Q v z")
# The four remaining rows are the two compressed rows, the extending
# fourth row, and the all-ones padding row. v,z are its two high entries.
M = [(f[0],f[1],P+a*v,P+a*z), (g[0],g[1],Q+b*v,Q+b*z),
     (u[0],u[1],v,z), (1,1,1,1)]
gamma = expand(sum(prod(M[i][j] for i,j in enumerate(p)) for p in permutations(range(4))))
A2 = 2*(b*(f[0]+f[1])+a*(g[0]+g[1])+a*b*(u[0]+u[1]))
A1 = gamma.coeff(v).coeff(z,0)
A0 = gamma.subs({v:0,z:0})
assert expand(gamma-A0-A1*(v+z)-A2*v*z) == 0
one = {k:1 for k in (f[0],f[1],g[0],g[1],u[0],u[1])}
assert expand(A2.subs(one)-4*(a+b+a*b)) == 0
assert A2.subs(one).subs({a:-Rational(1,2), b:-Rational(1,2)}) == -3
assert expand((B-C)*(2*(b*B+a*C)+2*(B+C))).subs(
    {a:C/(B-C),b:-B/(B-C)}).cancel() == 0
print("Verified both polarizations, the full padded cofactor, the base value and the seed slope.")
