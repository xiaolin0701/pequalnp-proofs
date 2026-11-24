"""Independent integer matching sums for the divided characteristic-two model."""

from itertools import combinations
from math import prod
from random import Random


def elementary(x, k):
    return sum(prod(t) for t in combinations(x, k))


def rook_coefficients(x):
    states = [1] + [0]*31
    for row in x:
        new = states[:]
        for mask, value in enumerate(states):
            for j, a in enumerate(row):
                if not mask & (1 << j):
                    new[mask | (1 << j)] += value*a
        states = new
    result = [0]*6
    for mask, value in enumerate(states):
        result[bin(mask).count("1")] += value
    return result


def centered(xs):
    return [*xs, -sum(xs)]


def check():
    rng = Random(210)
    for _ in range(600):
        b, c, *top = [centered([rng.randrange(-4,5) for _ in range(4)]) for _ in range(6)]
        d = [*top, [-sum(col) for col in zip(*top)]]
        x = [[b[i]+c[j]+2*d[i][j] for j in range(5)] for i in range(5)]
        _, r1, r2, r3, r4, r5 = rook_coefficients(x)
        e, f = elementary(b, 2), elementary(c, 2)
        def contract(p, q):
            return sum(b[i]**p * d[i][j] * c[j]**q for i in range(5) for j in range(5))
        h = contract(1, 1)
        last = e*elementary(c,3)+f*elementary(b,3)+(e+f)*h+contract(3,1)+contract(1,3)
        assert r1 == 0 and r2 == 4*(rook_coefficients(d)[2]+5*e+5*f)
        assert (r3-2*h) % 4 == 0
        assert (r4-4*e*f) % 8 == 0 and (r5-4*last) % 8 == 0
    print("600 integer arrays passed the exact quadratic identity and all three congruences.")


if __name__ == "__main__":
    check()
