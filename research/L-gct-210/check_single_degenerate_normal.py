"""Exact scalar checks for the degenerate common-normal theorem."""

import itertools
import sympy as sp

x, C, D, F = sp.symbols("x C D F")
elementary = [1, 1, 0, C, D, F]
powers = [5]
for k in range(1, 7):
    value = sum((-1)**(i+1)*elementary[i]*powers[k-i] for i in range(1,min(k,6)))
    if k<=5:
        value += (-1)**(k+1)*k*elementary[k]
    powers.append(sp.expand(value))


def trace(poly):
    return sp.expand(sum(c*powers[m[0]] for m,c in sp.Poly(poly,x).terms()))


d = x*x-x
h = x**3-x*x
k = C-h
assert trace(d*d).subs(C,0) == -4*D
assert sp.expand(trace(k*k).subs(D,0)) == 2*C*C-4*F
assert sp.expand(trace(d*h).subs({C:0,D:0})) == 5*F
assert sp.expand(trace(h*h).subs({C:0,D:0})) == -4*F

p = sp.symbols("p:5")
e = lambda vals, n: sum(sp.prod(choice) for choice in itertools.combinations(vals,n))
A2 = sp.Matrix([e(p[:i]+p[i+1:],2) for i in range(5)])
A3 = sp.Matrix([e(p[:i]+p[i+1:],3) for i in range(5)])
inv = sp.ones(5)/4-sp.eye(5)
pair = (A2.T*inv*A3)[0] + e(p,2)*e(p,3)/2
assert sp.expand(pair.subs({p[4]:0,p[3]:-sum(p[:3])})) == 0
A = sp.Matrix.hstack(*[2*sp.eye(5)[:,i]-sp.ones(5,1) for i in range(4)])
B = sp.Matrix.hstack(*[sp.eye(5)[:,i]+sp.eye(5)[:,4] for i in range(4)])
assert A.T*inv*B == sp.ones(4)/2-2*sp.eye(4)
assert (A.T*inv*B).rank() == 3

y, c = sp.symbols("y c")
with_coeff = (1+y*y)*(y**4+c/2)-2*y**6
assert sp.expand(with_coeff.subs(c,2*y**4*(y-1))-y**5*(y-1)**2) == 0
assert sp.expand((y**10-(y**4+c/2)**2).subs(c,2*y**4*(y-1))) == 0
print("Degenerate common-normal coefficient checks passed.")
