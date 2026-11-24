"""Cross-check the four-block formulas and all F2 points of the 14-plane."""

from itertools import permutations
from random import Random


def dot(x, y):
    return bin(x & y).count("1") % 2


def linear(columns, x):
    result = 0
    for j, v in enumerate(columns):
        if x >> j & 1:
            result ^= v
    return result


def sharp(x):
    return ((x & 5) << 1) | ((x & 10) >> 1)


def symplectic(x, y):
    return dot(x, sharp(y))


def determinant(columns):
    result = 0
    for order in permutations(range(len(columns))):
        if all((col >> j) & 1 for col, j in zip(columns, order)):
            result ^= 1
    return result


def matching_parities(columns):
    # State 'mask' records which of the five matrix rows have been matched.
    states = [1] + [0] * 31
    for column in columns:
        new = states[:]
        for mask, parity in enumerate(states):
            if parity:
                available = column & ~mask
                while available:
                    bit = available & -available
                    new[mask | bit] ^= 1
                    available ^= bit
        states = new
    result = [0] * 6
    for mask, p in enumerate(states):
        result[bin(mask).count("1")] ^= p
    return result[1:]


def build_basis():
    e = 31
    u, v = 3, 6
    rest = [x for x in range(1, 32) if not dot(x, e) and not dot(x, u) and not dot(x, v)]
    s = rest[0]
    t = next(x for x in rest if dot(s, x))
    return [e,u,v,s,t]


basis = build_basis()
adapted = {linear(basis, x): x for x in range(32)}
assert len(adapted) == 32


def original_columns(b, c, d):
    block = [c << 1] + [(v << 1) | ((b >> j) & 1) for j, v in enumerate(d)]
    return [linear(basis, linear(block, adapted[1 << j])) for j in range(5)]


def check():
    rng = Random(210)
    for _ in range(1200):
        b, c, *d = [rng.randrange(16) for _ in range(6)]
        block = [c << 1] + [(v << 1) | ((b >> j) & 1) for j, v in enumerate(d)]
        result = [0, symplectic(d[0], d[1]) ^ symplectic(d[2], d[3]),
                  symplectic(c, linear(d, sharp(b))), determinant(d), determinant(block)]
        assert matching_parities(original_columns(b, c, d)) == result
    lagrangian = (0, 1, 4, 5)
    for code in range(1 << 14):
        b = code & 15
        c = lagrangian[(code >> 4) & 3]
        d = [lagrangian[(code >> (6+2*i)) & 3] for i in range(4)]
        assert matching_parities(original_columns(b, c, d)) == [0]*5
    print("1200 independent block checks and all 16384 binary points of the 14-plane passed.")


if __name__ == "__main__":
    check()
