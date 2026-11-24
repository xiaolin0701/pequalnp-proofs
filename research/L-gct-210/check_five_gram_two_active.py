"""Check the two-active endpoint v_0=-1 at a good fifth cyclotomic prime."""

from itertools import combinations
from math import prod

from flint import nmod_mat, nmod_poly


def main():
    prime, root = 31, 2
    v = [-pow(root, i, prime) % prime for i in range(5)]
    assert len(set(v)) == 5 and pow(root, 5, prime) == 1
    inverse = lambda x: pow(x % prime, -1, prime)
    cinv = [
        [
            (1 + x + z - 4 * x * z - 5 * (i == j)) * inverse(5) % prime
            for j, z in enumerate(v)
        ]
        for i, x in enumerate(v)
    ]
    assert all(all(row) for row in cinv)
    theta = [0, 0] + [v[i] * inverse(cinv[1][i]) % prime for i in (2, 3, 4)]
    assert len(set(theta[2:])) == 3

    def dot(x, y):
        return sum(a * b for a, b in zip(x, y)) % prime

    def triple(x, y, z):
        return (
            sum(x) * sum(y) * sum(z)
            - dot(x, y) * sum(z)
            - dot(y, z) * sum(x)
            - dot(x, z) * sum(y)
            + 2 * sum(a * b * c for a, b, c in zip(x, y, z))
        ) % prime

    cubic = []
    quartics = []
    f = nmod_poly([0, 1], prime)
    for h in range(5):
        c = [0, 0, 1, h, -(v[2] + h * v[3]) * inverse(v[4]) % prime]
        assert dot(c, v) == 0
        x = [dot(row, c) for row in cinv]
        y = [dot(row, [a * b for a, b in zip(c, theta)]) for row in cinv]
        cubic.append(
            [triple(x, x, x), 3 * triple(x, x, y), 3 * triple(x, y, y), triple(y, y, y)]
        )
        tilted = [a * f + b for a, b in zip(x, y)]
        quartics.append(
            sum((prod(q) for q in combinations(tilted, 4)), nmod_poly([], prime))
        )

    assert int(nmod_mat(cubic[:4], prime).det()) == 4
    assert quartics[0].degree() == 4
    # The first two homogeneous quartics have no common point even over F_31 bar.
    assert quartics[0].gcd(quartics[1]) == nmod_poly([1], prime)
    print("Cubic determinant 4 mod 31; two homogeneous quartics have no common zero.")


if __name__ == "__main__":
    main()
