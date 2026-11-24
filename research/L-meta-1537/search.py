#!/usr/bin/env python3
"""Exhaust the L-meta-1537 triangle shard by necessary singleton-support transitions."""
from collections import Counter
from itertools import combinations, product


def cardinal(mask):
    return bin(mask).count("1")


def points_and_lines():
    normalized = [v for v in product(range(3), repeat=3)
                  if any(v) and next(x for x in v if x) == 1]
    lines = []
    for l in normalized:
        lines.append(sum(1 << i for i, p in enumerate(normalized)
                         if sum(a * b for a, b in zip(l, p)) % 3 == 0))
    assert len(normalized) == len(set(lines)) == 13
    assert all(cardinal(l) == 4 for l in lines)
    assert all(cardinal(l & m) == 1 for l, m in combinations(lines, 2))
    assert all(sum((l >> i & 1) and (l >> j & 1) for l in lines) == 1
               for i, j in combinations(range(13), 2))
    return lines


def submasks(mask):
    current = mask
    while True:
        yield current
        if not current:
            return
        current = (current - 1) & mask


def first_line_transitions(line, lines, all_points):
    """Check every possible pair of exact singleton supports creating this line first."""
    joins = meets = 0
    proper = [a for a in submasks(line) if a != line]
    for a in proper:
        for b in proper:
            if a | b != line:
                continue
            joins += 1
            # A wide proper subset of this line cannot belong to any other line.
            wide = max((a, b), key=cardinal)
            assert cardinal(wide) >= 2
            assert all(wide & ~other for other in lines if other != line)

    outside = all_points ^ line
    for extra_a in submasks(outside):
        if not extra_a:
            continue
        for extra_b in submasks(outside ^ extra_a):
            if not extra_b:
                continue
            a = line | extra_a
            b = line | extra_b
            assert a != b and a & b == line
            # Both operand wires lie outside every possible H, even for unknown
            # escapable lines, since each strictly contains four collinear points.
            assert cardinal(a) > 4 and cardinal(b) > 4
            meets += 1
    assert joins and meets
    return joins, meets


def reachable(max_paid, number_lines):
    """Forget restriction on creation of a partial or a mixed support, enlarging the search."""
    # State = (lines acquired, lines with an available wide proper subset, mixed wire count).
    states = {(0, 0, 0)}
    target = (1 << number_lines) - 1
    sizes = []
    for step in range(max_paid + 1):
        sizes.append(len(states))
        if any(full == target for full, _, _ in states):
            return True, sizes
        if step == max_paid:
            break
        new = set(states)
        for full, partial, mixed in states:
            new.add((full, partial, min(2, mixed + 1)))
            for i in range(number_lines):
                bit = 1 << i
                new.add((full, partial | bit, mixed))
                if partial & bit or mixed >= 2:
                    new.add((full | bit, partial, mixed))
        states = new
    return False, sizes


def main():
    lines = points_and_lines()
    all_points = (1 << 13) - 1
    arc_sizes = Counter(cardinal(x) for x in range(all_points + 1)
                        if all(cardinal(x & line) <= 2 for line in lines))
    assert arc_sizes[1] == 13
    transitions = [first_line_transitions(line, lines, all_points) for line in lines]
    assert len(set(transitions)) == 1
    triangular = 0
    for triple in combinations(lines, 3):
        if triple[0] & triple[1] & triple[2]:
            continue
        triangular += 1
        # Failure gives 2(g−|H|)<3|B|≤9, hence at most four non-H gate occurrences.
        found, sizes = reachable(4, len(triple))
        assert not found
    assert triangular == 234
    print("arc cardinalities:", sorted(arc_sizes.items()), "total", sum(arc_sizes.values()))
    print("proper OR/AND ordered operand pairs for each line:", transitions[0])
    print("triangle triples:", triangular, "reachable states by budget 0..4:", sizes)
    print("EXHAUSTED: no three leaking lines of the triangle shard can violate the inequality.")


if __name__ == "__main__":
    main()
