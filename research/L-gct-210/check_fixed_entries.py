"""Exact certificate for five or seven stationary entries. Requires SymPy."""

from collections import Counter
from itertools import combinations_with_replacement, permutations
from math import prod

from sympy import Matrix, eye, ones, zeros


orders = list(permutations(range(5)))
transforms = [
    [sum(1 << order[j] for j in range(5) if mask >> j & 1) for mask in range(32)]
    for order in orders
]
allowed_rows = [mask for mask in range(32) if mask.bit_count() <= 3]
inverse_factor = ones(5) - 4 * eye(5)


def patterns(size):
    for rows in combinations_with_replacement(allowed_rows, 5):
        if sum(mask.bit_count() for mask in rows) != size:
            continue
        if any(sum(mask >> j & 1 for mask in rows) > 3 for j in range(5)):
            continue
        if any(tuple(sorted(transform[mask] for mask in rows)) < rows for transform in transforms):
            continue
        yield rows


def constraints(rows):
    result = []
    for i, mask in enumerate(rows):
        for j in range(5):
            if mask >> j & 1:
                unit = zeros(5)
                unit[i, j] = 1
                result.append(unit)
    return result + [ones(5)]


def dual(form):
    return inverse_factor * form * inverse_factor


def gram(forms):
    vectors = Matrix.hstack(*(form.reshape(25, 1) for form in forms))
    duals = Matrix.hstack(*(dual(form).reshape(25, 1) for form in forms))
    return vectors.T * duals


def permanent(matrix):
    return sum(prod(matrix[i, order[i]] for i in range(5)) for order in orders)


def derivative(matrix):
    return Matrix(5, 5, lambda i, j: sum(
        prod(matrix[k, order[k]] for k in range(5) if k != i)
        for order in orders if order[i] == j
    ))


for size, expected in [(5, {6: 28}), (7, {8: 91, 7: 4})]:
    ranks = Counter()
    repairs = Counter()
    for rows in patterns(size):
        forms = constraints(rows)
        matrix = gram(forms)
        rank = len(forms) if matrix.det(method="domain-ge") else matrix.rank()
        ranks[rank] += 1
        if rank == len(forms):
            continue
        assert size == 7 and rank == 7
        coefficients, = matrix.nullspace()
        radical = sum((c * dual(f) for c, f in zip(coefficients, forms)), zeros(5))
        assert any(radical)
        at_one = ones(5) + radical
        value = permanent(at_one)
        if value != 120:
            repairs["permanent"] += 1
            print(rows, "permanent", value)
            continue
        extended = forms + [derivative(ones(5) + t * radical) for t in range(1, 5)]
        extended_rank = gram(extended).rank()
        assert extended_rank >= 8
        repairs["gradient"] += 1
        print(rows, "gradient rank", extended_rank)
    assert ranks == expected
    if size == 7:
        assert repairs == {"permanent": 2, "gradient": 2}
    print(size, "stationary entries, ranks", dict(sorted(ranks.items())))
