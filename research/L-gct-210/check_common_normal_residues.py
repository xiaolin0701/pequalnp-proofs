"""Certify common normals by reduction of the operator algebra modulo a prime.

For each normalized b up to permuting its five coordinates, test the sufficient
condition in CommonRowColumnNormals.md. A successful rank test also applies to
every normalized rational b reducing to those residues. A smaller modular rank
does not certify the characteristic-zero rank. Uses the Python standard library.
"""
import argparse
from collections import Counter
from itertools import combinations_with_replacement
from math import isqrt


def multiply(a, b, p):
    columns = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) % p for col in columns] for row in a]


def inverse(a, p):
    n = len(a)
    rows = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        k = next(i for i in range(j, n) if rows[i][j] % p)
        rows[j], rows[k] = rows[k], rows[j]
        scale = pow(rows[j][j], -1, p)
        rows[j] = [x * scale % p for x in rows[j]]
        for i in range(n):
            if i != j:
                c = rows[i][j]
                rows[i] = [(x-c*y) % p for x, y in zip(rows[i], rows[j])]
    return [row[n:] for row in rows]


def algebra_dimension(b, p):
    # b is nonconstant, sorted with b[-1] nonzero and sum(b) = 1 mod p.
    u = [[int(i == j) for i in range(4)] + [-b[j] * pow(b[4], -1, p) % p]
         for j in range(4)]
    pure = []
    for j in range(1, 4):
        v = [int(i == j) for i in range(5)]
        v[4] = (b[0]-b[j]) * pow(b[4]-b[0], -1, p) % p
        v[0] = -1-v[4]
        pure.append(v)
    ut = list(zip(*u))
    gram = [[(sum(x)*sum(y)-sum(i*j for i, j in zip(x, y))) % p for y in u]
            for x in u]
    igram = inverse(gram, p)
    generators = []
    for h in pure:
        d = [[(h[i]+h[j]) % p if i != j else 0 for j in range(5)] for i in range(5)]
        generators.append(multiply(igram, multiply(u, multiply(d, ut, p), p), p))

    pivots = {}
    basis = []

    def insert(matrix):
        v = [x for row in matrix for x in row]
        for j in sorted(pivots):
            if v[j]:
                factor = v[j]
                v = [(a-factor*c) % p for a, c in zip(v, pivots[j])]
        j = next((i for i, x in enumerate(v) if x), None)
        if j is not None:
            factor = pow(v[j], -1, p)
            pivots[j] = [x*factor % p for x in v]
            basis.append(matrix)

    insert([[int(i == j) for j in range(4)] for i in range(4)])
    pos = 0
    while pos < len(basis) and len(basis) < 16:
        for generator in generators:
            insert(multiply(basis[pos], generator, p))
        pos += 1
    return len(basis)


def scan(p):
    if p < 7 or any(p % n == 0 for n in range(2, isqrt(p)+1)):
        raise ValueError("Choose a prime greater than five.")
    ranks = Counter()
    patterns = Counter()
    for b in combinations_with_replacement(range(p), 5):
        if sum(b) % p != 1 or max(Counter(b).values()) >= 4:
            continue
        if (4*sum(x*x for x in b) - 1) % p == 0:
            continue
        rank = algebra_dimension(b, p)
        ranks[rank] += 1
        if rank < 16:
            patterns[tuple(sorted(Counter(b).values(), reverse=True))] += 1
    print(f"p={p}  algebra dimensions {dict(sorted(ranks.items()))}", flush=True)
    print(f"p={p}  inconclusive multiplicity patterns {dict(sorted(patterns.items()))}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", nargs="+", type=int)
    for prime in parser.parse_args().primes:
        scan(prime)
