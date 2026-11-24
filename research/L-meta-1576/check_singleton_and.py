"""Check the one-AND singleton case on all 8192 inputs of the F01 instance."""
from collections import Counter
from itertools import combinations

N = 13
lines = [{(t + d) % N for d in (0, 1, 3, 9)} for t in range(N)]
variables = [
    sum(1 << x for x in range(1 << N) if x & (1 << v)) for v in range(N)
]
all_assignments = (1 << (1 << N)) - 1
outside_zero = all_assignments
for v in set(range(N)) - lines[0]:
    outside_zero &= variables[v]
domain = variables[0] | variables[1] | outside_zero


def line_or(points):
    signal = 0
    for point in points:
        signal |= variables[point]
    return signal


repairs = Counter()
for a, b in combinations(range(N), 2):
    term = variables[a] & variables[b]
    possibles = set()
    for t, line in enumerate(lines):
        target = line_or(line)
        # If omitting several points is possible, adding all but one of them
        # still meets the upper bound and keeps the same truth values.
        for p in line:
            candidate = line_or(line - {p}) | term
            if ((candidate ^ target) & domain) == 0:
                possibles.add((t, p))
    assert len(possibles) <= 1, (a, b, possibles)
    repairs[len(possibles)] += 1

assert repairs == {0: 42, 1: 36}, repairs
print("78 AND gates checked on 8192 inputs: 42 allow no omission, 36 allow exactly one")
