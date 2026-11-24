"""Exact scalar identities for ThreeEqualRowNormal.md."""

from itertools import product, permutations
import sympy as sp

roots = (1, sp.I, -1, -sp.I, 0)
matching = sum(
    roots[i] * roots[j] * roots[k]**3 * roots[m]**3
    for i, j, k, m in permutations(range(5), 4)
)
assert sp.simplify(matching) == 8
three_row_factors = [(2,-1,-1), (-1,2,-1), (-1,-1,2)]
for u, v in product(three_row_factors, repeat=2):
    assert sum(x*y for x, y in zip(u,v)) != 0
for u, v, w in product(three_row_factors, repeat=3):
    assert sum(u[i]*v[j]*w[k] for i,j,k in permutations(range(3))) != 0

x, A, E, alpha, beta = sp.symbols("x A E alpha beta")
elementary = [1, 1, 0, 0, A, E]
powers = [5]
for k in range(1, 9):
    value = sum((-1)**(i+1)*elementary[i]*powers[k-i] for i in range(1,min(k,6)))
    if k <= 5:
        value += (-1)**(k+1)*k*elementary[k]
    powers.append(sp.expand(value))

def trace(poly):
    terms = sp.Poly(poly,x).terms()
    return sp.expand(sum(coef*powers[degree[0]] for degree,coef in terms))

d, h = x*(x-1), x**2*(x-1)
assert trace(d*d) == -4*A
assert trace(d*h) == 3*A+5*E
assert trace(h*h) == -4*E
t = h-alpha*d
y = (x-1)*(x-alpha)
assert sp.expand((trace(y)**2-trace(y*y))/2) == 6*alpha**2+2*A
four = trace(x*t)**2-trace((3*x*x-2*x)*t*t)
assert sp.expand(four-2*(2*A**2+3*A*alpha**2+11*E*alpha**2+8*E*alpha)) == 0
root_alpha = -(3+5*beta)/4
specialized = four.subs({A:-3*root_alpha**2,E:-3*beta*root_alpha**2,alpha:root_alpha})
assert sp.expand(specialized+sp.Rational(3,128)*(5*beta+3)**3*(55*beta**2-14*beta-9)) == 0
assert sp.gcd(25*beta**2+14*beta+9,(5*beta+3)*(55*beta**2-14*beta-9)) == 1
print("Three-equal-row coefficient checks passed.")
