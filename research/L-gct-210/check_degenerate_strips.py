"""Exact matching coefficients for the two degenerate-strip configurations.

Run with Python 3 and SymPy. In the three-support case all five positive
degrees are expanded. The general paired calculation checks the two cubic
coefficients used in the proof. No finite-field sampling is used.
"""
from itertools import combinations
from math import factorial, prod

from sympy import Poly, QQ, expand, factor, gcd_list, symbols


def disjoint_choices(first, second, k, h):
    """Choose k slots for the first vector and h disjoint slots for the second."""
    total = 0
    for left in combinations(range(5), k):
        remaining = [i for i in range(5) if i not in left]
        for right in combinations(remaining, h):
            total += prod(first[i] for i in left) * prod(second[i] for i in right)
    return total


def matching_sum(p, v, w, q, degree):
    # A matching of the rank-two matrix p*w^T+v*q^T designates k edges
    # of the first type. Their row sets and column sets can be paired in
    # k! ways, and the remaining degree-k edges in (degree-k)! ways.
    return sum(factorial(k)*factorial(degree-k) *
               disjoint_choices(p, v, k, degree-k) *
               disjoint_choices(w, q, k, degree-k)
               for k in range(degree+1))


a, b, d, e, t, c = symbols("a b d e t c")
v = [2, 2, 0, 0, -1]


def paired(t, x, y):
    return [t+x, t-x, -3*t+y, -3*t-y, 4*t]


def pure_three_support_check():
    p, q = paired(t, a, b), paired(c*t, d, e)
    coefficient_gcds = []
    for degree in range(1, 6):
        polynomial = Poly(matching_sum(p, v, v, q, degree), a, b, d, e, t)
        if degree <= 2:
            assert polynomial.is_zero
            coefficient_gcds.append(0)
            continue
        coefficient_gcds.append(gcd_list(polynomial.coeffs()))
        if degree == 3:
            assert expand(polynomial.coeff_monomial(a**2*t)-24*(c-2)) == 0
            assert expand(polynomial.coeff_monomial(d**2*t)+24*(2*c-1)) == 0
    for actual, expected in zip(coefficient_gcds[2:], [1, c, c+1]):
        assert Poly(actual, c, domain=QQ).monic() == Poly(expected, c, domain=QQ)
    print("Three-support pair, coefficient gcds up to nonzero scalars: 0, 0, 1, c, c+1")


def general_pair_check():
    x, y = symbols("x y")
    z = 3-2*x-2*y
    w = [x, x, y, y, z]
    q = [c*(y-z)*t+d, c*(y-z)*t-d, -c*(x-z)*t+e, -c*(x-z)*t-e, 2*c*(x-y)*t]
    polynomial = Poly(matching_sum(paired(t, a, b), v, w, q, 3), a, b, d, e, t)
    first = -24*(4*c*x+6*c*y-6*c-2*x+3)
    second = 24*(6*c*x+4*c*y-6*c+2*y-3)
    assert expand(polynomial.coeff_monomial(d**2*t)-first) == 0
    assert expand(polynomial.coeff_monomial(e**2*t)-second) == 0
    half_four = factor(disjoint_choices([a, -a, b, -b, 0], w, 2, 2))
    assert expand(half_four + y*(y+2*z)*a**2 + x*(x+2*z)*b**2) == 0
    print("General paired direction: two cubic coefficients and the quartic factor verified")


if __name__ == "__main__":
    pure_three_support_check()
    general_pair_check()
