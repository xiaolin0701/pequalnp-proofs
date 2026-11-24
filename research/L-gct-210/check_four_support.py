"""Check all support graphs in the rank-at-most-two part of the four-slot lemma.

A feasible graph must have a perfect matching along which at least three rows
can be made singletons in the enlarged product of the four row images.
Proof of the rank conditions used below is given in UpperTen.md.
"""
from itertools import combinations, permutations, product


def subsets(indices, size):
    return (sum(1 << i for i in s) for s in combinations(indices, size))


def check():
    perms = tuple(permutations(range(4)))
    sizes = [bin(mask).count("1") for mask in range(16)]
    all_masks = range(1, 16)
    counts = [0, 0, 0]
    for rows in product(all_masks, repeat=4):
        cols = [sum(1 << i for i, r in enumerate(rows) if r & (1 << j))
                for j in range(4)]
        if min(cols) == 0:
            continue
        col_degrees = [sizes[c] for c in cols]
        if sum(min(2, d) for d in col_degrees) < 7:
            continue
        row_degrees = [sizes[r] for r in rows]
        perfect = [p for p in perms if all(rows[i] & (1 << p[i]) for i in range(4))]
        for one_dim_row in range(4):
            dims = [2 if i != one_dim_row else 1 for i in range(4)]
            if max(col_degrees) <= 2 and all(a >= b for a, b in zip(row_degrees, dims)):
                assert perfect and sum(a > b for a, b in zip(row_degrees, dims)) <= 1
                counts[0] += 1
        if min(row_degrees) < 2 or max(col_degrees) > 3:
            continue
        assert perfect
        high = [j for j, d in enumerate(col_degrees) if d == 3]
        if len(high) <= 1:
            assert sum(d > 2 for d in row_degrees) <= 1
            counts[1] += 1
            continue
        high_bits = sum(1 << j for j in high)
        for q in range(2, 5):
            for special in subsets(range(4), q):
                if any(special & ~cols[j] for j in high):
                    continue
                if any((special & (1 << i)) and not (rows[i] & ~high_bits) for i in range(4)):
                    continue
                assert q == 2 and len(high) == 2
                assert all(row_degrees[i] == (3 if special & (1 << i) else 2)
                           for i in range(4))
                assert any(any((special & (1 << i)) and j not in high
                               for i, j in enumerate(p)) for p in perfect)
                counts[2] += 1
    assert counts[0] and counts[1] and counts[2]
    print("support cases independently checked", *counts)


if __name__ == "__main__":
    check()
