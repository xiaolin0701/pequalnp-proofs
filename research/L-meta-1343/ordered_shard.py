"""Apply independent-gate symmetry breaking strictly inside FIRSTJ segments."""
import argparse
import json
from pathlib import Path

def extend(cnf_path, meta_path, out, normalize_aliases=False):
    meta = json.loads(meta_path.read_text())
    gates = meta['gates']
    count = meta['vars']
    clauses = []
    def new():
        nonlocal count
        count += 1
        return count

    def equal_if_same(a, b):
        equal = new()
        for x, y in zip(a, b):
            clauses.append((-x, -y, equal))
        return equal

    def ordered(a, b, conditions=()):
        for high, x in enumerate(a):
            for y in b[:high]:
                clauses.append((*conditions, -x, -y))

    if normalize_aliases:
        # Normalize every constant/alias gate to an unused copy of input zero.
        # AND(x0,x0) is junk, OR(x0,x0) is not; choose to preserve the original flag.
        base = len(gates[0]['left'])
        for i,g in enumerate(gates):
            for operands in (g['left'],g['right']):
                clauses.extend([(-operands[base-2],),(-operands[base-1],)])
            for j in range(1,len(g['left'])):
                clauses.append((-g['left'][j],-g['right'][j]))
            dummy = new()
            clauses.append((-g['left'][0],-g['right'][0],dummy))
            clauses.append((-dummy,g['left'][0]))
            clauses.append((-dummy,g['right'][0]))
            clauses.append((-dummy,-meta['output'][i]))
            consumers = [operands[base+i] for nxt in gates[i+1:]
                         for operands in (nxt['left'], nxt['right'])]
            clauses.append((dummy, meta['output'][i], *consumers))
            for nxt in gates[i+1:]:
                for operands in (nxt['left'],nxt['right']):
                    clauses.append((-dummy,-operands[base+i]))

    for i in range(len(gates)-1):
        if i in (meta['first']-1, meta['first']):
            continue
        a, b = gates[i:i+2]
        # The right operand is always the larger one in the base encoding.
        ordered(a['right'], b['right'])
        equal_right = equal_if_same(a['right'], b['right'])
        ordered(a['left'], b['left'], (-equal_right,))
        equal_left = equal_if_same(a['left'], b['left'])
        # OR precedes AND on a tie of both inputs.
        clauses.append((-equal_right, -equal_left, -a['op_and'], b['op_and']))

    with cnf_path.open() as source, out.open('w') as target:
        old_header = source.readline().split()
        assert old_header == ['p', 'cnf', str(meta['vars']), str(meta['clauses'])]
        target.write(f'p cnf {count} {meta["clauses"]+len(clauses)}\n')
        for line in source:
            target.write(line)
        for clause in clauses:
            target.write(' '.join(map(str,clause)) + ' 0\n')
    print(f'{len(clauses)} ordering clauses, {count-meta["vars"]} auxiliaries')

def normalize(gates, first, output, base):
    """Return an equivalent re-indexed circuit for regression checking."""
    gates = list(gates)
    def swap_wire(w, lo):
        if w == lo:
            return lo+1
        if w == lo+1:
            return lo
        return w
    for _ in range(100000):
        for i in range(len(gates)-1):
            if i in (first-1, first):
                continue
            is_and_a, x, y = gates[i]
            is_and_b, u, v = gates[i+1]
            if (y, x, is_and_a) <= (v, u, is_and_b):
                continue
            lo = base+i
            assert v < lo   # the gates commute
            gates[i:i+2] = [gates[i+1],gates[i]]
            for j in range(i+2,len(gates)):
                is_and, p, q = gates[j]
                small, large = sorted((swap_wire(p,lo),swap_wire(q,lo)))
                gates[j] = is_and, small, large
            output = swap_wire(output,lo)
            break
        else:
            return gates, output
    raise RuntimeError('normalization failed to terminate')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('existing', type=Path)
    parser.add_argument('ordered', type=Path)
    parser.add_argument('--normalize-aliases', action='store_true')
    args = parser.parse_args()
    extend(args.existing, args.existing.with_suffix('.json'), args.ordered, args.normalize_aliases)
