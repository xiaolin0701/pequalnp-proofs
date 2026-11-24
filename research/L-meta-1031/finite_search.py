"""Generate exact-size SAT instances for the finite L-meta-1031 examples."""
import argparse
from itertools import combinations, permutations, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "L-meta-1343"))
from shard import Encoding


CYCLE_FIVE = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]
CYCLE_SIX = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]
EXAMPLES = {
    "cycle6twoadjacent": (8, CYCLE_SIX + [(0, 6), (1, 7)]),
    "cycle6twoopposite": (8, CYCLE_SIX + [(0, 6), (3, 7)]),
    "cycle5threeconsecutive": (8, CYCLE_FIVE + [(0, 5), (1, 6), (2, 7)]),
    "cycle5leaf": (6, CYCLE_FIVE + [(0, 5)]),
    "cycle5path2": (7, CYCLE_FIVE + [(0, 5), (5, 6)]),
    "cycle5plusedge": (7, CYCLE_FIVE + [(5, 6)]),
    "theta233": (7, [(0, 2), (2, 1), (0, 3), (3, 4),
                     (4, 1), (0, 5), (5, 6), (6, 1)]),
}


def extremal_inputs(n, edges):
    edge_masks = [1 << u | 1 << v for u, v in edges]
    independent = {
        mask for mask in range(1 << n)
        if not any(mask & edge == edge for edge in edge_masks)
    }
    maximal = sorted(
        mask for mask in independent
        if all(mask >> i & 1 or (mask | 1 << i) not in independent for i in range(n))
    )
    return maximal, edge_masks


def graph_automorphisms(n, edges):
    edges = {tuple(sorted(e)) for e in edges}
    degrees = [sum(i in e for e in edges) for i in range(n)]
    groups = [[v for v in range(n) if degrees[v] == d] for d in sorted(set(degrees))]
    original = [v for group in groups for v in group]
    for parts in product(*(permutations(group) for group in groups)):
        image = [v for part in parts for v in part]
        permutation = dict(zip(original, image))
        if all(tuple(sorted((permutation[u], permutation[v]))) in edges for u, v in edges):
            yield permutation


def instance(n, edges, count, path, prune_minimum=False, unique_or=()):
    negative, positive = extremal_inputs(n, edges)
    if not count or {i for e in edges for i in e} != set(range(n)):
        raise ValueError("These instances require positive gate count and no isolated vertices")
    cnf = Encoding()
    truth = [[bool(mask & (1 << i)) for i in range(n)] for mask in negative + positive]
    choices = []
    gate_types = []
    automorphisms = list(graph_automorphisms(n, edges))

    for gate in range(count):
        width = n + gate
        left, right = cnf.one(width), cnf.one(width)
        for a in range(width):
            for b in range(a + 1):
                cnf.add(-left[a], -right[b])
        if gate == 0:
            for a, b in combinations(range(n), 2):
                orbit = (tuple(sorted((f[a], f[b]), reverse=True)) for f in automorphisms)
                if (b, a) != min(orbit):
                    cnf.add(-left[a], -right[b])

        conjunction = cnf.new()
        witnesses = [[[], []], [[], []]]
        for index, row in enumerate(truth):
            a = cnf.mux(left, row)
            b = cnf.mux(right, row)
            out = cnf.new()
            cnf.add(-conjunction, -out, a)
            cnf.add(-conjunction, -out, b)
            cnf.add(-conjunction, out, -a, -b)
            cnf.add(conjunction, out, -a)
            cnf.add(conjunction, out, -b)
            cnf.add(conjunction, -out, a, b)
            if prune_minimum:
                # AND bypasses increase the circuit and must fail on a maximal
                # independent set. OR bypasses decrease it and must fail on an edge.
                phase = int(index >= len(negative))
                for side, (x, y) in enumerate(((a, b), (b, a))):
                    witness = cnf.new()
                    cnf.add(-witness, x)
                    cnf.add(-witness, -y)
                    witnesses[phase][side].append(witness)
            row.append(out)
            if gate == count - 1:
                cnf.add(-out if index < len(negative) else out)
        if prune_minimum:
            for side in range(2):
                cnf.add(-conjunction, *witnesses[0][side])
                cnf.add(conjunction, *witnesses[1][side])
            # Any direct child paired with either of its own inputs yields
            # an absorption/associativity identity, and is bypassable.
            for old, previous in enumerate(choices):
                for select in previous:
                    for wire in range(len(select)):
                        cnf.add(-right[n + old], -left[wire], -select[wire])
        choices.append((left, right))
        gate_types.append(conjunction)

    for leaf in unique_or:
        readers = []
        for (left, right), conjunction in zip(choices, gate_types):
            for select in (left[leaf], right[leaf]):
                cnf.add(-select, -conjunction)
                readers.append(select)
        for a, b in combinations(readers, 2):
            cnf.add(-a, -b)

    # Every primary is essential. Every nonoutput gate of a minimum circuit is live.
    for wire in range(n + count - 1):
        cnf.add(*(side[wire] for pair in choices for side in pair if wire < len(side)))

    # Choose the lexicographically smallest ready gate in the topological order.
    # The order's key is (larger predecessor, smaller predecessor).
    for (last_left, last_right), (left, right) in zip(choices, choices[1:]):
        for b, previous in enumerate(last_right):
            for smaller in right[:b]:
                cnf.add(-previous, -smaller)
            for a, prior_left in enumerate(last_left):
                for smaller in left[:a]:
                    cnf.add(-previous, -right[b], -prior_left, -smaller)
    cnf.dimacs(path)
    return cnf.variables, len(cnf.clauses)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", choices=EXAMPLES)
    parser.add_argument("gates", type=int)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("--prune-minimum", action="store_true")
    parser.add_argument("--critical-leaves", action="store_true", help="Apply the proved one-reader OR restriction to the three-leaf cycle at 10 gates")
    args = parser.parse_args()
    n, edges = EXAMPLES[args.graph]
    critical = {"cycle5threeconsecutive": (5, 6, 7), "cycle6twoadjacent": (6, 7), "cycle6twoopposite": (6, 7)}
    if args.critical_leaves and (args.graph not in critical or args.gates != 10):
        parser.error("The critical-leaf reduction is established only for this particular row")
    leaves = critical[args.graph] if args.critical_leaves else ()
    print(instance(n, edges, args.gates, args.cnf, args.prune_minimum, leaves))
