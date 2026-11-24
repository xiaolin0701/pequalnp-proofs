"""Exact checks for FourRowPurePlaneRelation.md."""

from itertools import permutations
from math import prod

import sympy as sp


def expand_groups(vector, weights):
    return tuple(x for x, m in zip(vector, weights) for _ in range(m))


def ordered_match(*rows):
    return sum(prod(row[j] for row, j in zip(rows, cols))
               for cols in permutations(range(len(rows[0])), len(rows)))


def inner(x, y):
    return sum(a*b for a, b in zip(x, y))


def check_root_lines():
    w = sp.symbols('w0:4')
    u, v, h, k = sp.symbols('u v h k')
    weights = (2, 1, 1, 1)
    ws = expand_groups(w, weights)
    for i, j in [(0, 1), (1, 2)]:
        q = [0]*4
        q[i], q[j] = weights[j], -weights[i]
        qs = expand_groups(q, weights)
        complement = [a for a in range(4) if a not in (i, j)]
        y = [0]*4
        z = [0]*4
        y[complement[0]], y[complement[1]] = u, v
        z[complement[0]], z[complement[1]] = h, k
        ys, zs = expand_groups(y, weights), expand_groups(z, weights)
        xx = [a-sum(ys)/3 for a in ys]
        vv = [a-sum(zs)/3 for a in zs]
        rhs = inner(qs, ws)*(inner(ys, zs)-sum(ys)*sum(zs)/3)
        assert sp.expand(ordered_match(qs, ws, xx, vv)-rhs) == 0


def check_gram_and_cofactor():
    d = sp.Symbol('d')
    rat = sp.Rational
    for weights in [(3, 1, 1), (2, 2, 1)]:
        L = sp.Matrix([[rat(1, m) if i == j else 0 for j in range(3)]
                       for i, m in enumerate(weights)])
        m = sp.Matrix(weights)
        Q = L-sp.ones(3)/4
        B = -Q/3-sp.ones(3)/240
        assert sp.trace(Q*B.inv()) == -10
        # Normalized vectors below are written by their physical entries.
        if weights == (3, 1, 1):
            p = sp.Matrix([rat(1, 3), 0, 0])
            sq = (p.T*sp.diag(*weights)*p)[0]
            assert sq-rat(1, 4) == rat(1, 12)
            assert sq/3-rat(11, 120) == rat(7, 360)
        else:
            p = sp.Matrix([rat(1, 4), rat(1, 4), 0])
            q = p + sp.Matrix([d, -d, 0])
            sq = (q.T*sp.diag(*weights)*q)[0]
            pq = (q.T*sp.diag(*weights)*p)[0]
            assert sp.expand(sq*rat(2, 3)-rat(41, 240)+rat(1, 240)-8*d*d/3) == 0
            assert -pq/3+rat(19, 240) == -rat(1, 240)

    a, b, c, e, f, g = sp.symbols('a b c e f g')
    tail = lambda A, B: (A+B, A+B, A-B, A-B)
    result = ordered_match(tail(1, a), tail(c, e), tail(f, g))
    result -= ordered_match(tail(1, b), tail(c, e), tail(f, g))
    assert sp.expand(result+8*(a-b)*(c*g+e*f)) == 0


def check_block_hessians():
    t, x, y, z, v = sp.symbols('t x y z v')
    blocks = [
        (t**2*(t*(y+z)+3*y*z), (y, z, t), 1-3*t, 6*t*t-3*t, {},
         432*t**5*(2*t-1)),
        (x*y*(x*y+2*z*(x+y)), (x, y, z), v, (3*v*v-2*v)/2, {z: 1-2*v},
         48*v**3*(v-1)*(2*v-1)*(3*v-2)),
    ]
    for quartic, coords, total, pair, other, expected in blocks:
        det = sp.hessian(quartic, coords).det()
        symmetric, rem, elementary = sp.symmetrize(det, coords[:2], formal=True)
        assert rem == 0
        s1, s2 = [item[0] for item in elementary]
        assert sp.expand(symmetric.subs({s1: total, s2: pair, **other}) - expected) == 0


if __name__ == '__main__':
    check_root_lines()
    check_gram_and_cofactor()
    check_block_hessians()
    print('Verified quartic on the roots, compressed Gram, and singleton cofactors.')
