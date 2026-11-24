"""Exhaustively bound coordinate subspaces in specified tensor-product bases over F_61.

Each factor basis comes from Fourier vectors on disjoint cycles or from a
recursively partitioned five-element set. Rank-one products within a pair of
bases are independent. A complex level family in these coordinates must also
satisfy the equations after reduction of the 60th roots of unity modulo 61.
"""

from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product

P = 61
ORDERS = list(permutations(range(5)))
PARTITIONS = [(5,), (4, 1), (3, 2), (3, 1, 1), (2, 2, 1), (2, 1, 1, 1), (1,)*5]


def normalize(values):
    scale = pow(next(x for x in values if x), -1, P)
    return tuple(x*scale % P for x in values)


@lru_cache(None)
def orbit(vector):
    return tuple(normalize(tuple(vector[i] for i in order)) for order in ORDERS)


def cycle_basis(sizes):
    offset = 0
    basis = []
    for size in sizes:
        for frequency in range(size):
            root = pow(2, (60//size)*frequency, P)
            basis.append((0,)*offset + tuple(pow(root, j, P) for j in range(size))
                         + (0,)*(5-offset-size))
        offset += size
    return tuple(basis)


@lru_cache(None)
def ordered_trees(size):
    if size == 1:
        return (1,)
    result = []
    for ncuts in range(1, size):
        for cuts in combinations(range(1, size), ncuts):
            ends = (0,) + cuts + (size,)
            result.extend(product(*(ordered_trees(j-i) for i,j in zip(ends, ends[1:]))))
    return tuple(result)


@lru_cache(None)
def tree_choices(tree):
    if tree == 1:
        return (((), (1,)),)
    result = []
    for children in product(*(tree_choices(t) for t in tree)):
        sizes = [len(carrier) for _,carrier in children]
        size = sum(sizes)
        rows = []
        start = 0
        for (child_rows, _), width in zip(children, sizes):
            rows.extend((0,)*start + row + (0,)*(size-start-width) for row in child_rows)
            start += width
        for frequency in range(1, len(children)):
            root = pow(2, 60//len(children)*frequency, P)
            rows.append(tuple(value*pow(root, j, P) % P
                              for j,(_, carrier) in enumerate(children) for value in carrier))
        carriers = [(pow(size, -1, P),)*size]
        carriers.extend(tuple(int(i == j) for i in range(size)) for j in range(size))
        result.extend((tuple(rows), carrier) for carrier in carriers)
    return tuple(result)


def bases_up_to_permutation():
    chosen, seen = [], set()
    def add(basis):
        rep = tuple(sorted(normalize(row) for row in basis))
        if rep not in seen:
            seen.update(tuple(sorted(rows)) for rows in zip(*(orbit(row) for row in rep)))
            chosen.append(rep)
    for sizes in PARTITIONS:
        add(cycle_basis(sizes))
    fourier_count = len(chosen)
    for tree in ordered_trees(5):
        for contrasts, carrier in tree_choices(tree):
            add(contrasts+(carrier,))
    return chosen, fourier_count


@lru_cache(None)
def matching_values(rows):
    if not rows:
        return {0: 1}
    result = {}
    for mask, coefficient in matching_values(rows[:-1]).items():
        for j, value in enumerate(rows[-1]):
            if value and not (mask >> j) & 1:
                key = mask | (1 << j)
                result[key] = (result.get(key, 0)+coefficient*value) % P
    return result


@lru_cache(None)
def matching_sum(rows):
    return sum(matching_values(rows).values()) % P


def maximum_dimension(left, right):
    directions = list(product(left, right))
    @lru_cache(None)
    def allowed(support):
        for repeats in range(6-len(support)):
            for extra in combinations_with_replacement(support, repeats):
                u, v = zip(*(directions[i] for i in support+extra))
                if matching_sum(tuple(sorted(u))) * matching_sum(tuple(sorted(v))) % P:
                    return False
        return True

    best = 0
    def visit(current, candidates):
        nonlocal best
        best = max(best, len(current))
        while len(current) + len(candidates) > best:
            first, *candidates = candidates
            constraints = [s for k in range(min(3, len(current))+1)
                           for s in combinations(current, k)]
            compatible = [j for j in candidates
                          if all(allowed(s+(first,j)) for s in constraints)]
            visit(current+(first,), compatible)
    visit((), [i for i in range(25) if allowed((i,))])
    return best


def main():
    bases, cycle_count = bases_up_to_permutation()
    largest = cycle_largest = count = 0
    for i, left in enumerate(bases):
        for j in range(i, len(bases)):
            value = maximum_dimension(left, bases[j])
            largest = max(largest, value)
            if j < cycle_count:
                cycle_largest = max(cycle_largest, value)
            count += 1
    print(f"{len(bases)} factor bases, {count} unordered pairs. "
          f"Maximum with two cycle bases: {cycle_largest}. Overall maximum: {largest}.")


if __name__ == "__main__":
    main()
