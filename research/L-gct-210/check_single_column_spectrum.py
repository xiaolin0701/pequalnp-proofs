"""Verify the pure-column spectral obstruction by Groebner bases over Q."""

import sympy as sp

x, z, A, B, C, D = sp.symbols("x z A B C D")
f = x**5 + A*x**3 + B*x**2 + C*x + D
g = sp.expand(5*x*sp.diff(f, x) - 9*f)
e3 = 8*A*x**3 - 8*B*x**2 - 4*C*x + 45*D
e4 = 6*A*x**3 - B*x**2 - 23*C*x + 90*D

# Coefficients of f(x) times the eigenvector's elementary symmetric functions.
coefficients = {5:1, 3:A, 2:B, 1:C, 0:D}
product = sp.expand(sum(coef*x**degree*(z-sp.Rational(1,3))**degree
                        *(z+sp.Rational(1,2))**(5-degree)
                        for degree, coef in coefficients.items()))
for degree, numerator, scale in [(2,e3,sp.Rational(5,216)),(1,e4,sp.Rational(5,1296))]:
    assert sp.rem(product.coeff(z,degree) - scale*numerator,g,x) == 0

for substitutions, variables in [({A:0,B:1}, [C,D]), ({A:0,B:0,C:1}, [D])]:
    ring = sp.QQ.poly_ring(*variables)
    divisor = sp.Poly(g.subs(substitutions), x, domain=ring)
    remainder = sp.Poly(1, x, domain=ring)
    for factor in (f, sp.diff(g,x), sp.diff(g,x), e3, e4):
        remainder = (remainder*sp.Poly(factor.subs(substitutions),x,domain=ring)).prem(divisor)
    # The divisor's leading coefficient is the nonzero constant 16,
    # so taking a pseudo-remainder preserves all required vanishing.
    basis = sp.groebner(remainder.all_coeffs(),*variables,domain=sp.QQ,method="f5b")
    assert [p.as_expr() for p in basis.polys] == [1]

corner = {A:0, B:0, C:0, D:1}
assert sp.rem((f*sp.diff(g,x)**2*e3*e4).subs(corner),g.subs(corner),x) != 0
print("Both rational Groebner bases equal [1]; the final projective point is excluded.")
