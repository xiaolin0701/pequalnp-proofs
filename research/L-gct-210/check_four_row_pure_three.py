"""Verify the matching polarizations and compressed endpoint identities exactly."""

from itertools import permutations, product
from math import prod

import sympy as sp


def ordered(*rows):
    return sum(prod(row[j] for row, j in zip(rows, cols))
               for cols in permutations(range(len(rows[0])), len(rows)))


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def shift(a, n):
    return tuple(x - sp.Rational(1, n)*sum(a) for x in a)


def check_transform():
    basis = [tuple(int(r == j) for r in range(5)) for j in range(5)]
    roots = [tuple(a-b for a, b in zip(node, basis[-1])) for node in basis[:-1]]
    for a, b in product(basis, repeat=2):
        x, y = shift(a, 3), shift(b, 3)
        assert sum(x)*sum(y)-dot(x, y) == 5*sp.Rational(1, 9)*sum(a)*sum(b)-dot(a, b)
        ax, bx = shift(a, 2), shift(b, 2)
        for p in roots:
            assert ordered(p, a, b) == 2*sum(c*i*j for c, i, j in zip(p, ax, bx))


def check_two_blocks():
    r, s, a, C, D, E = sp.symbols('r s a C D E')
    p = (r, s, -r-s)
    delta = (r, -s, -r+s)
    form = C*dot(p, p)+2*a*D*dot(p, delta)+a**2*E*dot(delta, delta)
    assert sp.expand(form/2-C*(r*r+s*s+r*s)-2*a*D*(r*r-s*s)-a*a*E*(r*r+s*s-r*s)) == 0
    l, m, n = sp.symbols('l m n')
    gram = sp.Matrix([[5*l*l/9-n, 5*l*m/9], [5*l*m/9, 5*m*m/9-m]])
    assert sp.expand(gram.det()-m*(n*(9-5*m)-5*l*l)/9) == 0
    for m in (1, 2, 3):
        n = 5-m
        for l in range(-n, n+1, 2):
            assert n*(9-5*m)-5*l*l != 0


def check_three_block_derivative():
    # The changed block is first, with any 2 or 3 physical coordinates;
    # the two remaining blocks have arbitrary positive sizes.
    for m in (2, 3):
        for n in range(1, 5-m):
            blocks = (m, n, 5-m-n)
            def expand(values):
                return tuple(v for v, size in zip(values, blocks) for _ in range(size))
            r = tuple(sp.symbols('r:5'))
            u = expand((0, *sp.symbols('u:2')))
            z = expand(sp.symbols('z:3'))
            p = (1, -1, 0, 0, 0)
            actual = ordered(p, shift(u, 3), shift(r, 3), shift(z, 3))
            expected = dot(p, r)*(dot(u, z)-sum(u)*sum(z)/3+2*sum(u)*z[0]/3)
            assert sp.expand(actual-expected) == 0


if __name__ == '__main__':
    check_transform()
    check_two_blocks()
    check_three_block_derivative()
    print('Verified row transformation, two-block forms, and the three-block quartic.')
