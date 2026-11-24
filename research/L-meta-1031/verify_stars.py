"""Build the minimum-cover star circuits and check every Boolean input and owner."""
from itertools import combinations

from finite_search import EXAMPLES


def star_circuit(n, edges):
    for size in range(n + 1):
        cover = next((c for c in combinations(range(n), size)
                      if all(u in c or v in c for u, v in edges)), None)
        if cover is not None:
            break
    leaves = {c: [] for c in cover}
    for u, v in edges:
        center, leaf = (u, v) if u in cover else (v, u)
        leaves[center].append(leaf)
    gates = []

    def add(operation, left, right):
        gates.append((operation, left, right))
        return n + len(gates) - 1

    def disjoin(wires):
        current, *rest = wires
        for other in rest:
            current = add("or", current, other)
        return current

    centers = {}
    for c, neighborhood in leaves.items():
        assert neighborhood
        centers[add("and", c, disjoin(neighborhood))] = c
    output = disjoin(centers)
    assert len(gates) == len(edges) + len(cover) - 1
    return cover, gates, output, centers


def check(n, edges):
    cover, gates, output, centers = star_circuit(n, edges)
    owned = {wire: [] for wire in centers}
    masks = {1 << u | 1 << v: (u, v) for u, v in edges}
    for mask in range(1 << n):
        wires = [bool(mask >> i & 1) for i in range(n)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
        assert wires[output] == any(mask & edge == edge for edge in masks)
        if mask in masks:
            for wire in centers:
                if wires[wire]:
                    owned[wire].append(masks[mask])
    for wire, c in centers.items():
        assert owned[wire] and all(c in edge for edge in owned[wire])
        pending = list(gates[wire - n][1:])
        while pending:
            w = pending.pop()
            if w >= n:
                assert gates[w - n][0] == "or"
                pending.extend(gates[w - n][1:])
    return len(gates), len(cover)


if __name__ == "__main__":
    for name, (n, edges) in EXAMPLES.items():
        gates, cover = check(n, edges)
        print(f"{name}: {gates} gates, cover {cover}, {1 << n} inputs and all owners checked")
