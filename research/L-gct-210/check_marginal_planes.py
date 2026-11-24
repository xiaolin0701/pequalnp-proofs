"""Enumerate projective additive-marginal directions and lines at good primes."""

import argparse
from itertools import combinations, combinations_with_replacement, permutations
from math import prod


def symmetric_coefficients(v, p):
    return tuple(sum(prod(c) for c in combinations(v, k)) % p for k in range(2, 6))


def normalize(v, p):
    inverse = pow(next(t for t in v if t), -1, p)
    return tuple(inverse*t % p for t in v)


def roots_in_field(coefficients, p):
    poly = [1, 0, coefficients[0], -coefficients[1], coefficients[2], -coefficients[3]]
    roots = []
    for r in range(p):
        while len(poly) > 1:
            divided = [poly[0]]
            for a in poly[1:]:
                divided.append((a+r*divided[-1]) % p)
            if divided[-1]:
                break
            roots.append(r)
            poly = divided[:-1]
    return tuple(roots) if len(roots) == 5 else ()


def point_catalogue(p):
    points = set()
    anchors = []
    for triple in combinations_with_replacement(range(p), 3):
        last = (-1-sum(triple)) % p
        if last < triple[-1]:
            continue
        row = tuple(sorted((1, *triple, last)))
        q, r, s, t = symmetric_coefficients(row, p)
        complementary = (-q % p, -r % p, (3*pow(10, -1, p)*q*q-s) % p,
                         (pow(5, -1, p)*q*r-t) % p)
        col = roots_in_field(complementary, p)
        cols = set(permutations(col)) if col else set()
        if not cols:
            continue
        rows = [b for b in set(permutations(row)) if next(x for x in b if x) == 1]
        points.update(b+c for b in rows for c in cols)
        anchors.append(rows[0]+col)
    return points, anchors


def check(p):
    points, anchors = point_catalogue(p)
    if p > 20:
        import numpy as np
        vectors = np.array(list(points), dtype=np.int32)

    for anchor in anchors:
        if p > 20:
            # A line through this point lies in the tangent hyperplanes of
            # e2(b)+e2(c) and e3(b)+e3(c). All directions have zero sums.
            a = np.array(anchor, dtype=np.int32)
            keep = (vectors @ a % p == 0) & (vectors @ (a*a % p) % p == 0)
            candidates = map(tuple, vectors[keep].tolist())
        else:
            candidates = points
        for other in candidates:
            if anchor == other:
                continue
            if all(normalize(tuple((a+k*b) % p for a,b in zip(anchor, other)), p) in points
                   for k in range(1, 6)):
                raise AssertionError(f'projective line at {p}: {anchor}, {other}')
    print(f'F_{p}: {len(points)} projective points, {len(anchors)} permutation representatives, no lines.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('primes', type=int, nargs='*', default=[7, 11, 13])
    for prime in parser.parse_args().primes:
        if prime < 7 or any(prime % i == 0 for i in range(2, int(prime**0.5)+1)):
            raise ValueError('Use a prime of at least seven.')
        check(prime)
