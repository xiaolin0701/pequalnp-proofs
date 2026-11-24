"""Hessians and radical witnesses in the vanishing ternary branch."""

from itertools import combinations, product
from math import prod

import sympy as sp


def physical(z):
    return sp.Matrix([sum(z)-3*x for x in z])


def hessian(x):
    return sp.Matrix(5, 5, lambda i, j: 0 if i == j else sum(
        x[k]*x[l] for k, l in combinations(set(range(5))-{i, j}, 2)))


def polar(x, y):
    return (hessian(x+y)-hessian(x)-hessian(y))/2


def main():
    a, b, c, t = sp.symbols('a b c t')
    det = lambda z: sp.expand(hessian(physical(z)).det(method='domain-ge'))
    two = det((a, b, 0, 0, 0))
    assert sp.expand(two+486*(a-2*b)*(a+b)**4*(2*a-b)*(a*a-a*b+b*b)**2) == 0
    four = det((a, b, c, -a-b-c, 0))
    assert sp.expand(four + 354294*(a*b*c*(a+b+c))**2
                     *(a*a+b*b+c*c+a*b+b*c+c*a)) == 0
    three = det((a, b, c, 0, 0))
    roots = [-1, 2, sp.Rational(1, 2), (1+sp.sqrt(-3))/2, (1-sp.sqrt(-3))/2]
    surviving = {(u, v) for u, v in product(roots, repeat=2)
                 if all(sp.expand(three.subs({a: u+v*k, b: 1, c: k})) == 0
                        for k in (1, 2, 3, 4))}
    assert surviving == {(-1, -1), (roots[3], roots[4]), (roots[4], roots[3])}
    u = physical((-1, 1, 0, 0, 0))
    v = physical((-1, 0, 1, 0, 0))
    e = sp.ones(5, 1)
    for x, y, ray in [(u, e+v, (1, 1, 0, 0, 0)), (v, e+u, (1, 0, 1, 0, 0)),
                       (u-v, e-u+2*v, (0, 1, 1, 0, 0))]:
        form = polar(x, y)
        assert form.rank() == 4 and form*sp.Matrix(ray) == sp.zeros(5, 1)
    five = sp.Poly(det((a, b, c, t, -t)), t)
    s1, s2, s3 = sp.symbols('s1 s2 s3')
    result, rem, _ = sp.symmetrize(five.nth(6), (a, b, c), formal=True)
    assert rem == 0
    assert sp.expand(result.subs(s3, s1*s2/9)+39366*(s1*s1-3*s2)**2) == 0
    assert sp.resultant(two.subs(b, 1), (a+1)**2-9*a, a) != 0
    row_sum, pair, triple, d, T = sp.symbols('row_sum pair triple d T')
    block = sp.Matrix([[12*row_sum, 3*row_sum, 3*pair], [3*row_sum, 0, pair],
                       [3*pair, pair, triple]])
    assert sp.expand(block.det()-3*row_sum*(2*pair**2-3*row_sum*triple)) == 0
    root_polynomial = T**5+3*T**4+2*T**3-2*d*T**2-3*d*T-d
    assert sp.expand(root_polynomial-(T+1)*(T**3*(T+2)-d*(2*T+1))) == 0
    p, q = sp.symbols('p q')
    pencil = sp.Matrix([[1+t*p, t*q], [t*q, t]])
    assert sp.expand(pencil.det()-(t+t**2*(p-q*q))) == 0
    print('Checked Hessians, 25 candidate planes, three kernels, and the missing-cell identities.')


if __name__ == '__main__':
    main()
