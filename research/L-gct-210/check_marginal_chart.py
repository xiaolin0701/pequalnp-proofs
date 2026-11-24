"""Independently test the serialized chart equations against integer rook sums."""

from pathlib import Path
from random import Random
from math import prod

from check_rescaled_matching import elementary, rook_coefficients


def parse_polynomial(expression, names):
    terms = []
    for monomial in expression.rstrip(',').split('+'):
        coefficient, *factors = monomial.split('*')
        powers = []
        for factor in factors:
            name, _, exponent = factor.partition('^')
            powers.append((names.index(name), int(exponent or '1')))
        terms.append((int(coefficient), powers))
    return terms


def evaluate(terms, coordinates):
    return sum(c*prod(coordinates[j]**p for j,p in powers) for c,powers in terms)


def check(filename):
    names, field, *expressions = filename.read_text().splitlines()
    names = names.split(',')
    prime = int(field)
    groups = []
    for k in range(2,6):
        current, expressions = expressions[:k+1], expressions[k+1:]
        groups.append([parse_polynomial(s, names) for s in current])
    assert not expressions
    rng = Random(210+prime)
    for _ in range(120):
        coords = [rng.randrange(prime) for name in names]
        x, y = rng.randrange(prime), rng.randrange(prime)
        images = [coords[i]*x+coords[i+1]*y for i in range(0,12,2)]
        b = [x, y, *images[:2]]
        c = images[2:]
        b.append(-sum(b))
        c.append(-sum(c))
        actual = [sum(evaluate(f, coords) * x**(k-i) * y**i
                      for i,f in enumerate(group)) for k,group in enumerate(groups, start=2)]
        _, r1, r2, r3, r4, r5 = rook_coefficients([[v+w for w in c] for v in b])
        E, C, Q, F = actual
        q, t = elementary(b,2), elementary(b,3)
        # Undo the lower-degree eliminations in the fourth and fifth equations.
        diffs = (r1, r2-20*E, r3-60*C, r4-12*(Q+3*q*E),
                 r5-24*F-12*(q*C+t*E))
        assert all(i % prime == 0 for i in diffs)
    print(f'{filename.name} passed 120 integer matching-sum comparisons.')


if __name__ == '__main__':
    for filename in sorted((Path(__file__).parent/'marginal-plane-search').glob('chart*.in')):
        check(filename)
