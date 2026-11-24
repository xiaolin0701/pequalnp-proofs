"""Exact checks of the coefficient identities in FourByFive3222.md."""

from itertools import combinations, permutations, product
from math import prod


def unit(size, index):
    return tuple(int(i == index) for i in range(size))


def diff(x, y):
    return tuple(a - b for a, b in zip(x, y))


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def ordered_matches(rows, omit=None):
    cols = set(range(len(rows[0]))) - {omit}
    return sum(
        prod(row[j] for row, j in zip(rows, js))
        for js in permutations(cols, len(rows))
    )


def deleted(rows):
    return tuple(ordered_matches(rows, j) for j in range(len(rows[0])))


def cubic_vector(a, b):
    return tuple(
        2 * x * y - sum(a) * y - sum(b) * x + sum(a) * sum(b) - dot(a, b)
        for x, y in zip(a, b)
    )


def elementary(x, k):
    return sum(prod(js) for js in combinations(x, k))


def check_cubic_and_quartic():
    # Both expressions are bilinear; checking all coordinate basis pairs suffices.
    for size in [4, 5]:
        for i, j in product(range(size), repeat=2):
            a, b = unit(size, i), unit(size, j)
            assert deleted((a, b)) == cubic_vector(a, b)

    row = [unit(4, i) for i in range(4)]
    factors = {
        deleted((diff(row[i], row[2]), diff(row[j], row[3]), diff(row[k], row[3])))
        for i, j, k in product(range(2), repeat=3)
    }
    assert {(2, 0, 0, 0), (0, 2, 0, 0), (2, 0, -2, 0), (1, 1, -1, -1)} <= factors
    for a, b in [(1, 2), (1, 3)]:
        first, second = diff(row[0], row[a]), diff(row[0], row[b])
        cof = deleted((first, second, second))
        assert {i for i, value in enumerate(cof) if value} == set(range(4)) - {0, a, b}

    # 10 is a square root of -1 in F_101. The two parameters occur bilinearly.
    z = (0, 1, 10, -1, -10)
    e = unit(5, 0)
    for a, b in product([0, 1], repeat=2):
        v = (a, *z[1:])
        w = (b, *z[1:])
        assert all((c - 2 * t * t) % 101 == 0 for c, t in zip(deleted((e, v, w)), z))

    # The three cases have zero sum, a double root, and five distinct roots.
    for prime, v in [(11, [1, 3, 4, 5, 9]), (43, [5, 14, 18, 18, 32]),
                     (67, [21, 32, 33, 54, 62])]:
        assert all(elementary(v, k) % prime == 0 for k in (2, 3, 4))
        assert elementary(v, 5) % prime != 0
        s = sum(v)
        h = [x * x - s * x for x in v]
        assert ordered_matches((v, v, h)) % prime == 0
        assert (ordered_matches((v, h, h)) - 10 * elementary(v, 5)) % prime == 0


def check_deleted_row_quadratic():
    # Three tail rows are centered, and row four can have arbitrary tail.
    # Coefficients are tested on every basis pair in the four row blocks.
    zero = (0,) * 4
    row = [unit(4, i) for i in range(4)]
    bases = [[diff(row[i], row[3]) for i in range(3)]] * 3 + [row]
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        k = 3 - i - j
        for a in range(4):
            for b in range(a + 1, 4):
                for x, y in product(bases[a], bases[b]):
                    tail = [zero] * 4
                    tail[a], tail[b] = x, y
                    # Each two-edge match of two of the three retained rows
                    # has two extensions on four columns.
                    def quad(omit):
                        return 0 if omit in (a, b) else 2 * ordered_matches((x, y))
                    expected = sum((tail[i][p] - tail[j][p]) * (tail[k][p] + tail[3][p])
                                   for p in range(4))
                    assert quad(i) - quad(j) == 2 * expected


if __name__ == "__main__":
    check_cubic_and_quartic()
    check_deleted_row_quadratic()
    print("Deleted matching coefficients and all three tail pairings verified.")
