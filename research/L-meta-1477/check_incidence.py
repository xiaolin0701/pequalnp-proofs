"""Check the posted edge list and every monomial of the 125-gate star circuit."""
import ast
import json
import re
import sys
from pathlib import Path

instance = json.loads(Path(sys.argv[1]).read_text())['gap']
posted = re.search(r'\(\[(\(0, 21\).*?)\] : List \(ℕ × ℕ\)\)', instance['statement'])
assert posted is not None
edges = set(ast.literal_eval('[' + posted[1] + ']'))
offsets = (0, 5, 7, 17, 20)
matchings = [{(row, 21 + (row + offset) % 21) for row in range(21)}
             for offset in offsets]
assert set.union(*matchings) == edges and len(edges) == 105
assert {(i-j) % 21 for i in offsets for j in offsets if i != j} == set(range(1, 21))
gates = []
values = [{frozenset([v])} for v in range(42)]
def gate(op, left, right):
    a, b = values[left], values[right]
    values.append((a | b) if op == 'OR' else {x | y for x in a for y in b})
    gates.append(op)
    return len(values) - 1
stars = []
for row in range(21):
    neighbors = sorted(v for u, v in edges if u == row)
    accumulator = neighbors[0]
    for v in neighbors[1:]:
        accumulator = gate('OR', accumulator, v)
    stars.append(gate('AND', row, accumulator))
output = stars[0]
for star in stars[1:]:
    output = gate('OR', output, star)
assert values[output] == {frozenset(pair) for pair in edges}
assert gates.count('AND') == 21 and gates.count('OR') == 104
print('105 posted incidences; 5 disjoint perfect matchings; no four-cycle')
print('125 gates: 104 OR, 21 AND; all output monomials equal the posted edges')
