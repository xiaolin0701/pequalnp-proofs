"""Finite checks for the partner of the first possible AND parent in L-meta-3136.

The four compressed inputs of the parent are x1, x7, x8, and x0 OR x3.
Rows in this file are concrete nine-bit assignments. A column is an integer
whose j-th bit is the value of one signal on row j. All formulas in the
enumerator have AND/OR gates and at most one occurrence per listed leaf.
A negated signal is introduced explicitly when testing the one-NOT cases.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement


EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (5, 7), (6, 8), (8, 5))
EDGE_ROWS = tuple((1 << a) | (1 << b) for a, b in EDGES)
PARENT_INPUTS = (1 << 1, 1 << 7, 1 << 8, 9)
PARENT = 395


def bits(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


def graph(row):
    return any(row & edge == edge for edge in EDGE_ROWS)


def tree_masks():
    """Two non-root intermediates of each commutative four-leaf OR tree."""
    for a, b in combinations(PARENT_INPUTS, 2):
        other = [c for c in PARENT_INPUTS if c not in (a, b)]
        for c in other:
            yield a | b, a | b | c
        if a == PARENT_INPUTS[0]:
            yield a | b, other[0] | other[1]


class Rows:
    def __init__(self, add_all_ones=False):
        negatives = [x for x in range(512) if x & PARENT and not graph(x)
                     and all(graph(x | (1 << i)) for i in range(9) if not x >> i & 1)]
        positives = EDGE_ROWS + ((511,) if add_all_ones else ())
        self.rows = positives + tuple(negatives)
        self.full = (1 << len(self.rows)) - 1
        self.pos = (1 << len(positives)) - 1
        self.raw = tuple(self.column(1 << i) for i in range(9))

    def column(self, variable_mask):
        return sum(1 << j for j, x in enumerate(self.rows) if variable_mask & x)

    @lru_cache(None)
    def formula(self, cols, pos):
        """Can a read-once monotone formula separate the labelled rows?"""
        neg = self.full ^ pos
        n = len(cols)
        # above[j][S] contains rows >= row j on the columns selected by S.
        above = [[self.full] * (1 << n) for _ in self.rows]
        for j, row in enumerate(above):
            for s in range(1, 1 << n):
                bit = s & -s
                col = cols[bit.bit_length() - 1]
                row[s] = row[s ^ bit] & (col if col >> j & 1 else self.full)

        @lru_cache(None)
        def fit(s, p, q):
            if not s:
                return False
            if any(above[j][s] & q for j in bits(p)):
                return False
            if any(not (p & ~cols[i] or q & cols[i]) for i in bits(s)):
                return True
            a = (s - 1) & s
            while a:
                b = s ^ a
                if a < b:
                    # At an OR root assign each positive row to a child allowed
                    # to accept it. At an AND root assign negative rows dually.
                    for is_or in (True, False):
                        label, common = (p, q) if is_or else (q, p)

                        def eligible(side):
                            if is_or:
                                return sum(1 << j for j in bits(label) if not above[j][side] & common)
                            return sum(1 << j for j in bits(label)
                                       if all(not (above[k][side] >> j & 1) for k in bits(common)))

                        left, right = eligible(a), eligible(b)
                        if left | right != label:
                            continue
                        flex = left & right
                        choice = flex
                        while True:
                            lrows = (label & ~right) | choice
                            rrows = label ^ lrows
                            if is_or:
                                if fit(a, lrows, common) and fit(b, rrows, common):
                                    return True
                            elif fit(a, common, lrows) and fit(b, common, rrows):
                                return True
                            if not choice:
                                break
                            choice = (choice - 1) & flex
                a = (a - 1) & s
            return False

        return fit((1 << n) - 1, pos, neg)

    def shared_patterns(self, cols, inside, polarity):
        """Necessary truth tables for a shared internal signal on these rows.

        Collapsing a source-disjoint subtree to h loses distinctions inside
        its source set. For positive/negative rows ordered on all remaining
        sources, the outer monotone formula must distinguish them via h. With
        both h and NOT h available, their h values have to be different.
        """
        values = [sum(((c >> j) & 1) << i for i, c in enumerate(cols)) for j in range(len(self.rows))]
        outside = ((1 << len(cols)) - 1) ^ inside
        relations = defaultdict(list)

        def bind(a, b, parity):
            relations[a].append((b, parity))
            relations[b].append((a, parity))

        fixed = len(self.rows)
        for a, va in enumerate(values):
            for b in range(a + 1, len(values)):
                vb = values[b]
                if va & inside == vb & inside:
                    bind(a, b, 0)
                if self.pos >> a & 1 and not self.pos >> b & 1 and not va & ~vb & outside:
                    bind(a, b, 1)
                    if polarity:
                        bind(a, fixed, 1)  # The anchor is false.
        seen = {}
        components = []
        for index in [fixed] + list(range(fixed)):
            if index in seen:
                continue
            seen[index] = 0
            stack = [index]
            masks = [0, 0]
            while stack:
                a = stack.pop()
                if a != fixed:
                    masks[seen[a]] |= 1 << a
                for b, parity in relations[a]:
                    required = seen[a] ^ parity
                    if b in seen and seen[b] != required:
                        return
                    if b not in seen:
                        seen[b] = required
                        stack.append(b)
            components.append((masks[1],) if index == fixed else masks)
        possible = [0]
        for masks in components:
            possible = [a | b for a in possible for b in masks]
        for pattern in possible:
            if all(not pattern >> a & 1 or all(pattern >> b & 1 or va & ~vb & inside
                                               for b, vb in enumerate(values))
                   for a, va in enumerate(values)):
                yield pattern

    @lru_cache(None)
    def with_sharing(self, cols, repetitions):
        if self.formula(cols, self.pos):
            return True
        for s in range(1, (1 << len(cols)) - 1):
            if not s & (s - 1):
                continue  # Repeated source leaves are supplied by the caller.
            inner = tuple(cols[i] for i in bits(s))
            outer = tuple(v for i, v in enumerate(cols) if not s >> i & 1)
            for h in self.shared_patterns(cols, s, True):
                if not self.formula(inner, h):
                    continue
                for multiplicity in range(2, repetitions + 2):
                    tail = tuple(sorted(outer + (h,) * multiplicity))
                    extra = repetitions + 1 - multiplicity
                    if self.formula(tail, self.pos) or (extra and self.with_sharing(tail, extra)):
                        return True
        return False


def run():
    trees = list(tree_masks())
    assert len(trees) == 15
    extras = sorted({m for tree in trees for m in (9,) + tree})
    # Every original signal can change the required output while all three
    # reusable intermediates and the completed first parent stay fixed.
    for tree in trees:
        for i in range(9):
            assert any(x & PARENT and not graph(x) and graph(x | (1 << i)) and
                       all(bool(x & m) == bool((x | (1 << i)) & m) for m in (9,) + tree)
                       for x in range(512))

    mono = Rows()
    for tree in trees:
        for p, q in combinations((9,) + tree, 2):
            assert not mono.formula(mono.raw + (mono.column(p), mono.column(q)), mono.pos)
    for m in extras:
        extra = mono.column(m)
        baseline = mono.raw + (extra,)
        for repeated in baseline:
            assert not mono.formula(baseline + (repeated,), mono.pos)
        assert not mono.with_sharing(baseline, 1)
    for a, b in combinations_with_replacement(mono.raw, 2):
        assert not mono.formula(mono.raw + (a, b), mono.pos)
    for repeated in mono.raw:
        assert not mono.with_sharing(mono.raw + (repeated,), 1)
    assert not mono.with_sharing(mono.raw, 2)
    print("All monotone cases excluded on", len(mono.rows), "rows.", flush=True)

    one = Rows(add_all_ones=True)
    for m in extras:
        assert not one.formula(one.raw + (one.full ^ one.column(m),), one.pos)
    examined = 0
    for s in range(1, 1 << 9):
        inner = tuple(one.raw[i] for i in bits(s))
        outer = tuple(x for i, x in enumerate(one.raw) if not s >> i & 1)
        for h in one.shared_patterns(one.raw, s, False):
            examined += 1
            assert not (one.formula(inner, h) and one.formula(outer + (h, one.full ^ h), one.pos))
    print("All one-NOT cases excluded on", len(one.rows), "rows;", examined, "shared truth tables.")


if __name__ == "__main__":
    run()
