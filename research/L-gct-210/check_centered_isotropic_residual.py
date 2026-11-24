"""Exact arithmetic for CenteredIsotropicResidual.md."""

import itertools
import sympy as sp

x, h, t = sp.symbols("x h t")
low_poly = x**5-x**2-h

def trace(poly, modulus, powers):
    terms = sp.Poly(sp.rem(sp.expand(poly),modulus,x),x).terms()
    return sp.factor(sum(coef*powers[degree[0]] for degree,coef in terms))

def tr(poly):
    return trace(poly,low_poly,[5,0,0,3,0])

U = x**3-sp.Rational(3,5)-5*h*x/3
V = x**4-x-5*h*x*x/3
assert (tr(U*U),tr(U*V),tr(V*V)) == (sp.Rational(6,5),-25*h**2/3,-2*h)
q = 9*t*t-125*h*h*t-15*h
v, u = V+t*U, V+(125*h*h/9-t)*U

def reduce_t(poly):
    return sp.factor(sp.rem(sp.expand(poly),q,t))

mixed = reduce_t(tr(u*u*v))
assert sp.factor(mixed+h*(18*t-125*h*h)*(3125*h**3+108)/1215) == 0
z = sp.rem(sp.expand(v*(x**4-x)/h),low_poly,x)
p1,p2,p3 = tr(z),tr(z*z),tr(z**3)
err = reduce_t((p1**3-3*p1*p2+2*p3)/60-p1**3/125)
assert sp.factor(err-(3125*h**3+108)*(25*h*t+6)/10125) == 0
assert sp.factor(sp.resultant(18*t-125*h*h,q,t)/(3125*h**3+108)) == -45*h
assert sp.factor(sp.resultant(25*h*t+6,q,t)/(3125*h**3+108)) == 3

C, F = sp.Rational(5,2), -sp.Rational(3,2)
repeated_poly=x**5-C*x*x-F
def rep_tr(poly):
    return trace(poly,repeated_poly,[5,0,0,3*C,0])
k=x**3+x-sp.Rational(3,2)
b2=-rep_tr(k*k)/2
assert b2==-sp.Rational(15,4)
assert rep_tr(k**3)-2*k.subs(x,1)*b2 == -15
z=sp.rem(sp.expand(k*(x**4-C*x)/F),repeated_poly,x)
assert (rep_tr(z),rep_tr(z*z)+2*b2,rep_tr(z**3)+6*b2*z.subs(x,1)) == (5,5,35)

p=list(sp.symbols("p:4"))+[0]
def elementary(values,degree):
    return sum(sp.prod(choice) for choice in itertools.combinations(values,degree))
A2=sp.Matrix([elementary(p[:i]+p[i+1:],2) for i in range(5)])
A3=sp.Matrix([elementary(p[:i]+p[i+1:],3) for i in range(5)])
row_inverse=sp.ones(5)/4-sp.eye(5)
assert sp.expand(2*(A2.T*row_inverse*A3)[0]-6*sum(p)*elementary(p,4)
                 +elementary(p,2)*elementary(p,3)) == 0
for i in range(4):
    unit=sp.eye(5)[:,i]+sp.eye(5)[:,4]
    ci=p[i]**2-sum(p)*p[i]+elementary(p,2)/2
    assert sp.expand((A2.T*row_inverse*unit)[0]+ci) == 0
print("Centered isotropic residual spectrum and Gram checks passed.")
