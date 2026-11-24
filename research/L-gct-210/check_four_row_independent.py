"""Symbolically verify the polar cubic factors for the repeated two-cell branch."""

from itertools import combinations
from math import prod

import sympy as sp


def main():
    t, a, b, c, k = sp.symbols("t a b c k")
    ht, ha, hb, hc = sp.symbols("h_t h_a h_b h_c")
    variables = (t, a, b, c)
    high = (ht, ha, hb, hc)
    polynomial = t**2 * (a*b + a*c + b*c) + 2*t*a*b*c
    matching = sum(prod(cols) for cols in combinations((t, t, a, b, c), 4))
    assert sp.expand(polynomial - matching) == 0
    polar = sum(coef * sp.diff(polynomial, var) for coef, var in zip(high, variables))
    assert sp.expand(polar.subs(t, 0) - 2*ht*a*b*c) == 0
    tail_quad = sp.cancel(polar.subs(ht, 0) / t)
    assert sp.expand(tail_quad.subs(t, 0) - 2*(ha*b*c + hb*a*c + hc*a*b)) == 0

    endpoint = sp.expand(polar.subs(b, k*a + (1-k)*t))
    derivative = sp.diff(endpoint, c)
    assert sp.Poly(derivative, a).nth(2) == 2*k*ht
    predicted = t * (ha * (2*k*a + (3-2*k)*t) + hb * (2*a+t))
    assert sp.expand(derivative.subs(ht, 0) - predicted) == 0
    assert sp.expand(sp.det(sp.Matrix([[2*k, 2], [3-2*k, 1]])) - 6*(k-1)) == 0
    pure = endpoint.subs(dict(zip(high, (0, 0, 0, 1))))
    assert sp.expand(pure - t*((1-k)*t**2 + (3-k)*a*t + 2*k*a*a)) == 0
    print("Quartic, polar restriction, and one-parameter endpoint verified over Q[k].")


if __name__ == "__main__":
    main()
