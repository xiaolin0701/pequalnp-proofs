"""Compare generic five-row, five-column additive matching identities over Z."""

from itertools import combinations
from math import prod

from sympy.polys.domains import ZZ
from sympy.polys.rings import ring


def elementary(vector, degree, polynomials):
    return sum((prod(group, start=polynomials.one) for group in combinations(vector, degree)),
               polynomials.zero)


def matching_sums(rows, columns, polynomials):
    # Process one row at a time. A mask records exactly the used columns.
    states = {0: polynomials.one}
    for row in rows:
        updated = states.copy()
        for used, weight in states.items():
            for j, column in enumerate(columns):
                if used & (1 << j):
                    continue
                new_used = used | (1 << j)
                updated[new_used] = updated.get(new_used, polynomials.zero) + weight * (row + column)
        states = updated
    return [sum((weight for mask, weight in states.items() if mask.bit_count() == degree),
                polynomials.zero) for degree in range(6)]


def main():
    polynomials, *variables = ring('b0,b1,b2,b3,c0,c1,c2,c3', ZZ)
    rows = variables[:4] + [-sum(variables[:4], polynomials.zero)]
    columns = variables[4:] + [-sum(variables[4:], polynomials.zero)]
    b, c = ([elementary(vector, degree, polynomials) for degree in range(6)]
            for vector in (rows, columns))
    raw = matching_sums(rows, columns, polynomials)
    f2 = b[2] + c[2]
    f3 = b[3] + c[3]
    f4 = 10 * (b[4] + c[4]) - 3 * b[2]**2
    f5 = 5 * (b[5] + c[5]) - b[2] * b[3]
    expected = [20 * f2, 60 * f3, 12 * f4 + 36 * b[2] * f2,
                24 * f5 + 12 * (b[2] * f3 + b[3] * f2)]
    for degree, expression in enumerate(expected, 2):
        assert raw[degree] == expression, degree
        print(f'r_{degree}: all {len(raw[degree])} integer monomial coefficients agree.')


if __name__ == '__main__':
    main()
