"""Verify the second residue of the quartic as a generic 24-variable integer polynomial."""

from itertools import combinations
from math import prod

from sympy.polys.domains import ZZ
from sympy.polys.rings import ring


def centered(vector):
    return [*vector, -sum(vector)]


def elementary(vector, degree):
    return sum(prod(group) for group in combinations(vector, degree))


def matching(matrix, degree, polynomials):
    states = {0: polynomials.one}
    for row in matrix:
        updated = states.copy()
        for mask, coefficient in states.items():
            if mask.bit_count() == degree:
                continue
            for j, entry in enumerate(row):
                if mask & (1 << j):
                    continue
                new_mask = mask | (1 << j)
                updated[new_mask] = updated.get(new_mask, polynomials.zero) + coefficient * entry
        states = updated
    return sum(poly for mask, poly in states.items() if mask.bit_count() == degree)


def squared_block(vector, rows):
    return sum(vector[i] * vector[k] * sum(x*y for x, y in zip(rows[i], rows[k]))
               for i, k in combinations(range(5), 2))


def main():
    ring_names = [f'b{i}' for i in range(4)] + [f'c{i}' for i in range(4)]
    ring_names += [f'd{i}{j}' for i in range(4) for j in range(4)]
    polynomials, *variables = ring(','.join(ring_names), ZZ)
    b, c = centered(variables[:4]), centered(variables[4:8])
    d = [centered(variables[i:i+4]) for i in range(8, 24, 4)]
    d.append([-sum(column) for column in zip(*d)])
    cols = list(zip(*d))
    x = [[u+v+2*d[i][j] for j, v in enumerate(c)] for i, u in enumerate(b)]
    qb, qc = elementary(b, 2), elementary(c, 2)
    first = sum(b[i] * c[j] * (b[i]+c[j]) * d[i][j] for i in range(5) for j in range(5))
    phi = (elementary(b, 4) + elementary(c, 4) + first
           + (qb+qc)*matching(d, 2, polynomials) + squared_block(b, d) + squared_block(c, cols))
    quartic = matching(x, 4, polynomials)
    difference = quartic - 4*qb*qc - 8*phi
    assert all(coefficient % 16 == 0 for coefficient in difference.values())
    print(f'All coefficients agree modulo 16 in 24 variables; raw fourth matching has {len(quartic)} terms.')


if __name__ == '__main__':
    main()
