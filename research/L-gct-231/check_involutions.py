"""Check all Schubert charts for a 3-plane stable under a simultaneous involution."""

import argparse
from itertools import combinations, combinations_with_replacement
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from sympy.polys.domains import GF
from sympy.polys.rings import ring


PRIME = 13
PAIRS = list(combinations_with_replacement(range(4), 2))


def eigenspaces(permutation):
    positive, negative, seen = [], [], set()
    for i, j in PAIRS:
        if (i, j) in seen:
            continue
        mate = tuple(sorted((permutation[i], permutation[j])))
        orbit_sum = [0] * len(PAIRS)
        orbit_sum[PAIRS.index((i, j))] = 1
        orbit_sum[PAIRS.index(mate)] = 1
        positive.append(orbit_sum)
        if mate != (i, j):
            difference = orbit_sum.copy()
            difference[PAIRS.index(mate)] = -1
            negative.append(difference)
        seen.update(((i, j), mate))

    def total(vector):
        return sum((1 if i == j else 2) * x for (i, j), x in zip(PAIRS, vector))

    pivot = positive.pop(0)
    inverse = pow(total(pivot), -1, PRIME)
    centered = [[(x-total(row)*inverse*y) % PRIME for x, y in zip(row, pivot)] for row in positive]
    return centered, negative


def template(size, pivots):
    return [[int(j == lead) if j in pivots else (None if j > lead else 0)
             for j in range(size)] for lead in pivots]


def equation_strings(positive, negative, pivot_positive, pivot_negative):
    rows = template(len(positive), pivot_positive) + template(len(negative), pivot_negative)
    bases = [positive] * len(pivot_positive) + [negative] * len(pivot_negative)
    size = sum(x is None for row in rows for x in row)
    names = [f'x{i}' for i in range(size)] or ['unused']
    polynomials, *variables = ring(','.join(names), GF(PRIME))
    parameters = iter(variables)
    coordinates = []
    for row, basis in zip(rows, bases):
        terms = [next(parameters) if x is None else polynomials.ground_new(x) for x in row]
        coordinates.append([sum((t*v[j] for t, v in zip(terms, basis)), polynomials.zero)
                            for j in range(len(PAIRS))])
    matrix = [[tuple(v[PAIRS.index(tuple(sorted((i, j))))] for v in coordinates)
               for j in range(4)] for i in range(4)]
    states = {(0, (0, 0, 0)): polynomials.one}
    for row in matrix:
        updated = states.copy()
        for (used, degree), coefficient in states.items():
            for j, entry in enumerate(row):
                if used & (1 << j):
                    continue
                for k, linear in enumerate(entry):
                    if not linear:
                        continue
                    next_degree = list(degree)
                    next_degree[k] += 1
                    key = used | (1 << j), tuple(next_degree)
                    updated[key] = updated.get(key, polynomials.zero) + coefficient*linear
        states = updated
    equations = {}
    for (_, degree), coefficient in states.items():
        if sum(degree) >= 2:
            equations[degree] = equations.get(degree, polynomials.zero) + coefficient

    def serialize(poly):
        pieces = []
        for powers, coeff in poly.terms():
            factors = [str(int(coeff) % PRIME)]
            factors += [name + (f'^{d}' if d > 1 else '') for name, d in zip(names, powers) if d]
            pieces.append('*'.join(factors))
        return '+'.join(pieces)

    return names, [serialize(f) for f in equations.values() if f]


def check(permutation, singular, path):
    positive, negative = eigenspaces(permutation)
    count = 0
    for plus_dim in range(4):
        minus_dim = 3 - plus_dim
        if plus_dim > len(positive)//2 or minus_dim > len(negative)//2:
            continue
        for piv_plus in combinations(range(len(positive)), plus_dim):
            for piv_minus in combinations(range(len(negative)), minus_dim):
                names, equations = equation_strings(positive, negative, piv_plus, piv_minus)
                path.write_text(f'ring r={PRIME},({",".join(names)}),dp;\n'
                                f'ideal I={",".join(equations)}; option(redSB); ideal G=std(I);\n'
                                'if(size(G)==1 && G[1]==1){print("empty");}else{print("candidate");}\nquit;\n')
                result = run([singular, '-q', str(path)], capture_output=True, text=True, check=True)
                if result.stdout.strip() != 'empty':
                    raise AssertionError((permutation, piv_plus, piv_minus, result.stdout, result.stderr))
                count += 1
    return count


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--singular', default='Singular')
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        path = Path(tmp) / 'chart.sing'
        for permutation, expected in (([1, 0, 2, 3], 65), ([1, 0, 3, 2], 70)):
            count = check(permutation, args.singular, path)
            assert count == expected
            print(f'{permutation}: all {count} chart ideals are the unit ideal.', flush=True)


if __name__ == '__main__':
    main()
