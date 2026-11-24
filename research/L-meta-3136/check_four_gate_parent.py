"""Finite computations for a four-gate parent in L-meta-3136.

Run alongside check_early_parent.py with Python 3.9 or later. Truth tables in
prefix enumeration have 512 bits. Only the final read-once search projects
the partner onto its required positive and negative boundary assignments.
"""
from collections import Counter
from functools import lru_cache, reduce
from itertools import combinations
from operator import or_

import check_early_parent as checker


ALL = (1 << 512) - 1
RAW_MASKS = tuple(1 << i for i in range(9))
INITIAL_MASKS = RAW_MASKS + (9,)


def column(mask):
    return sum(1 << x for x in range(512) if x & mask)


RAW = tuple(column(m) for m in RAW_MASKS)
FREE = column(9)
POSITIVE = tuple(checker.graph(x) for x in range(512))


def four_gate_functions():
    """Every nonconstant majorant determined by at most five initial features."""
    functions = {}
    for support in combinations(INITIAL_MASKS, 5):
        projection = [sum(1 << i for i, m in enumerate(support) if x & m) for x in range(512)]
        unconstrained = set(projection) - {p for p, f in zip(projection, POSITIVE) if f}
        for n in range(1, len(unconstrained) + 1):
            for zeros in combinations(unconstrained, n):
                table = sum(1 << x for x, p in enumerate(projection) if p not in zeros)
                functions[table] = support
    covers = {}
    for table in functions:
        if all(not (table >> x & 1) or all(table >> (x | (1 << i)) & 1 for i in range(9))
               for x in range(512)):
            mask = sum(1 << i for i in range(9) if table >> (1 << i) & 1)
            assert column(mask) == table
            covers[mask] = table
    assert len(functions) == 22 and len(covers) == 14
    return covers


@lru_cache(None)
def or_trees(signals):
    if len(signals) == 1:
        return [()]
    output = []
    for n in range(1, len(signals)):
        for left in combinations(signals, n):
            if signals[0] not in left:
                continue
            right = tuple(m for m in signals if m not in left)
            output.extend(a + b + (reduce(or_, signals),)
                          for a in or_trees(left) for b in or_trees(right))
    return output


def new_covers(covers):
    tested = 0
    for leaves in combinations(INITIAL_MASKS, 5):
        parent = reduce(or_, leaves)
        if parent not in covers or parent in (395, 109):
            continue
        if any(reduce(or_, leaves[:i] + leaves[i + 1:]) == parent for i in range(5)):
            continue
        checker.PARENT = parent
        rows = checker.Rows()
        trees = or_trees(leaves)
        assert len(trees) == 105
        extras = set()
        for tree in trees:
            masks = set((9,) + tree[:-1])
            extras.update(masks)
            for i in range(9):
                assert any(x & parent and not checker.graph(x) and checker.graph(x | (1 << i))
                           and all(bool(x & m) == bool((x | (1 << i)) & m) for m in masks)
                           for x in range(512))
        for m in extras:
            assert not rows.formula(rows.raw + (rows.column(m),), rows.pos)
        assert not rows.with_sharing(rows.raw, 1)
        for v in rows.raw:
            assert not rows.formula(rows.raw + (v,), rows.pos)
        tested += 1
    assert tested == 12


def live_prefixes(sources, target):
    """All distinct three-wire environments before a fourth new gate.

    An ancestor bitset records which of the three prefix gates feed the last
    gate. Wires equal to an earlier wire can be substituted everywhere.
    """
    initial = len(sources)

    def visit(values, ancestors, used_not):
        g = len(values) - initial
        if g == 3:
            for i in range(len(values) - 1):
                if ancestors[-1] | ancestors[i] != 7:
                    continue
                if values[-1] & values[i] == target or values[-1] | values[i] == target:
                    yield tuple(sorted(values[initial:])), used_not
            if not used_not and ALL ^ values[-1] == target and ancestors[-1] == 7:
                yield tuple(sorted(values[initial:])), True
            return
        for i, a in enumerate(values):
            if not used_not:
                c = ALL ^ a
                if c not in values and c != target:
                    yield from visit(values + (c,), ancestors + (ancestors[i] | (1 << g),), True)
            for j, b in enumerate(values[:i]):
                for c in (a & b, a | b):
                    if c not in values and c != target:
                        deps = ancestors[i] | ancestors[j] | (1 << g)
                        yield from visit(values + (c,), ancestors + (deps,), used_not)

    yield from visit(sources, (0,) * initial, False)


def old_cover():
    checker.PARENT = 395
    target = column(395)
    known = tuple(column(m) for m in checker.PARENT_INPUTS)
    # With OR03 present, x1, x7 and x8 must also occur. Without it, the
    # raw five inputs of K must all occur directly. An invalid wire is false.
    domains = [tuple(RAW[i] for i in (0, 1, 3, 7, 8)), known + (0,)]
    domains.extend(known + (a,) for a in RAW if a not in known)
    signatures = set()
    for s in domains:
        for signature, used_not in live_prefixes(s, target):
            assert not used_not
            signatures.add(signature)
    assert len(signatures) == 207
    for a, b in checker.tree_masks():
        fixed = set(RAW + (0, FREE, column(a), column(b), target))
        extra = {x & y for x, y in combinations(fixed, 2)} | {x | y for x, y in combinations(fixed, 2)}
        signatures = {t for t in signatures if not (set(t) <= fixed or
                      (len(set(t) - fixed) == 1 and (set(t) - fixed) <= extra))}
    assert len(signatures) == 72
    assignments = [x for x in range(512) if x & 395]
    usable = set()
    for signature in signatures:
        env = RAW + (FREE,) + signature
        mandatory = tuple(i for i in range(9) if any(
            not checker.graph(x) and checker.graph(x | (1 << i))
            and all((v >> x & 1) == (v >> (x | (1 << i)) & 1) for v in env[9:])
            for x in assignments))
        remaining = [i for i in range(len(env)) if i not in mandatory]
        for n in range(11 - len(mandatory)):
            for added in combinations(remaining, n):
                cols = tuple(sorted(env[i] for i in mandatory + added))
                outputs = {}
                for x in assignments:
                    key = sum((v >> x & 1) << j for j, v in enumerate(cols))
                    if outputs.setdefault(key, POSITIVE[x]) != POSITIVE[x]:
                        break
                else:
                    usable.add(cols)
    assert Counter(map(len, usable)) == {9: 1, 10: 27}
    assert tuple(sorted(RAW)) in usable
    rows = checker.Rows()
    for cols in usable:
        if len(cols) == 10:
            projected = tuple(sum((v >> x & 1) << j for j, x in enumerate(rows.rows)) for v in cols)
            assert not rows.formula(projected, rows.pos)


if __name__ == "__main__":
    all_covers = four_gate_functions()
    new_covers(all_covers)
    old_cover()
    print("12 new OR covers (105 trees each) and the four-gate implementations of K1 checked.")
