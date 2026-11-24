"""Rational Newton and compressed-spectrum checks in CenteredIsotropicNormalOpen."""
import sympy as sp

x, C, D, F = sp.symbols("x C D F", nonzero=True)
moments = [5, 0, 0, 3*C, -4*D, 5*F, 3*C*C]
gram = sp.Matrix(3,3,lambda i,j:moments[i+j])
first = sp.Matrix(3,3,lambda i,j:moments[i+j+1])
second = sp.Matrix(3,3,lambda i,j:moments[i+j+2])
tr = -sp.trace(gram.inv()*first)
tr2 = -2*sp.trace(gram.inv()*second)+sp.trace((gram.inv()*first)**2)
assert sp.factor(tr-4*D/(3*C)) == 0
assert sp.factor((tr**2-tr2)/2-5*F/(3*C)) == 0

poly = x**5-C*x**2+D*x-4*D**2/(15*C)
def reduce(poly_in):
    return sp.factor(sp.rem(sp.expand(poly_in),poly,x))
def trace(poly_in):
    terms = sp.Poly(reduce(poly_in),x).terms()
    return sp.factor(sum(coef*moments[degree[0]] for degree,coef in terms))
def project(poly_in):
    cross = sp.Matrix([trace(poly_in*x**i) for i in range(3)])
    coefficients = gram.inv()*cross
    return reduce(poly_in-sum(number*x**i for i,number in enumerate(coefficients)))

v = project((x-2*D/(3*C))*project(x**3))
assert trace(v*v) == 0
assert sp.factor(trace(v**3)-2*D**3*(27*C**4-80*D**3)**2/(164025*C**8)) == 0
assert sp.factor(sp.discriminant(poly,x)-D**2*(27*C**4-80*D**3)**2/(405*C**4)) == 0
assert sp.factor((x**5-10*x*x+15*x-6)-(x-1)**3*(x*x+3*x+6)) == 0
print("Centered isotropic normal spectrum and trace checks passed.")
