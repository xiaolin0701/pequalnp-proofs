"""Independently enumerate the small support obstruction in ZeroPureColumnPivot.md."""
from itertools import combinations, combinations_with_replacement

for k in range(1, 6):
    full = (1 << k) - 1
    checked = 0
    survivors = 0
    for rows in combinations_with_replacement(range(full + 1), 5):
        checked += 1
        if full in rows or (rows[0] | rows[1] | rows[2] | rows[3] | rows[4]) != full:
            continue
        # A singleton available normal entry cannot repeat in the same column.
        if any(rows.count(full ^ (1 << j)) > 1 for j in range(k)):
            continue
        # A squarefree moment cannot have exactly one nonzero summand.
        if any(sum((r & s) == s for r in rows) == 1 for s in range(1, full+1)):
            continue
        # Two nonzero centered vectors that both live on the same two rows
        # are multiples of the same difference and cannot be orthogonal.
        column_supports = [{i for i, r in enumerate(rows) if r & (1 << j)} for j in range(k)]
        if any(len(a | b) <= 2 for a, b in combinations(column_supports, 2)):
            continue
        survivors += 1
    assert survivors == 0
    print(k, "positive pure columns:", checked, "row patterns,", survivors, "survivors")
