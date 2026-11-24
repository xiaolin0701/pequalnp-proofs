#!/usr/bin/env python3
"""Independent CNF reduction for the w1006 monotone circuit synthesis shard."""
import argparse
import itertools
import json
from pathlib import Path

N = 11
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
         (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
EDGE_MASKS = [(1 << u) | (1 << v) for u, v in EDGES]

def edge_function(mask):
    return any(mask & e == e for e in EDGE_MASKS)

def extremal_rows():
    independent = {mask for mask in range(1 << N) if not edge_function(mask)}
    maximal = sorted(mask for mask in independent if all(
        mask & (1 << i) or (mask | (1 << i)) not in independent for i in range(N)))
    return maximal, EDGE_MASKS

class Encoding:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def new(self):
        self.variables += 1
        return self.variables

    def add(self, *lits):
        self.clauses.append(lits)

    def one(self, n):
        choices = [self.new() for _ in range(n)]
        self.add(*choices)
        for a, b in itertools.combinations(choices, 2):
            self.add(-a, -b)
        return choices

    def mux(self, selectors, values):
        target = self.new()
        for select, value in zip(selectors, values):
            if type(value) is bool:
                self.add(-select, target if value else -target)
            else:
                self.add(-select, -target, value)
                self.add(-select, target, -value)
        return target

    def dimacs(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.variables} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(str(x) for x in clause) + ' 0\n')


def encode(gates, first, out):
    if not 0 <= first < gates - 1:
        raise ValueError('two distinct junk ANDs require first < gates - 1')
    negative, positive = extremal_rows()
    masks = negative + positive
    cnf = Encoding()
    # Wire IDs 0..10 are graph inputs, then two constant wires, then gates.
    wires = [[bool(mask & (1 << i)) for i in range(N)] + [False, True] for mask in masks]
    info = []
    junk = []
    for j in range(gates):
        width = N + 2 + j
        left, right = cnf.one(width), cnf.one(width)
        # AND and OR are commutative. Equality remains allowed for unary gates.
        for i in range(width):
            for h in range(i):
                cnf.add(-left[i], -right[h])
        op_and = cnf.new()
        outputs = []
        for row in wires:
            a, b = cnf.mux(left, row), cnf.mux(right, row)
            z = cnf.new()
            cnf.add(-op_and, -z, a)
            cnf.add(-op_and, -z, b)
            cnf.add(-op_and, z, -a, -b)
            cnf.add(op_and, z, -a)
            cnf.add(op_and, z, -b)
            cnf.add(op_and, -z, a, b)
            outputs.append(z)
            row.append(z)
        bad = outputs[:len(negative)]
        junk_gate = cnf.new()
        cnf.add(-junk_gate, op_and)
        cnf.add(-junk_gate, *bad)
        for z in bad:
            cnf.add(-op_and, -z, junk_gate)
        if j < first:
            cnf.add(-junk_gate)
        elif j == first:
            cnf.add(junk_gate)
        junk.append(junk_gate)
        info.append(dict(left=left, right=right, op_and=op_and))
    cnf.add(*junk[first + 1:])
    # Allow any gate to be output, including circuits followed by dead padding.
    output = cnf.one(gates)
    for j, select in enumerate(output):
        for idx, row in enumerate(wires):
            z = row[N + 2 + j]
            cnf.add(-select, -z if idx < len(negative) else z)
    cnf.dimacs(out)
    meta = dict(gates=info, output=output, first=first, negative=negative, positive=positive,
                vars=cnf.variables, clauses=len(cnf.clauses))
    out.with_suffix('.json').write_text(json.dumps(meta))
    print(f'{gates} gates, {len(negative)} maximal independent sets, {len(positive)} edges, '
          f'{cnf.variables} variables, {len(cnf.clauses)} clauses', flush=True)


def decode(meta_path, model_path):
    meta = json.loads(meta_path.read_text())
    true = set()
    for line in model_path.read_text().splitlines():
        if line.startswith('v '):
            true.update(int(x) for x in line.split()[1:] if int(x) > 0)
    def choice(options):
        found = [k for k, v in enumerate(options) if v in true]
        if len(found) != 1:
            raise ValueError(f'invalid one-hot choice: {found}')
        return found[0]
    gates = [(g['op_and'] in true, choice(g['left']), choice(g['right'])) for g in meta['gates']]
    out = choice(meta['output'])
    junk = set()
    for mask in range(1 << N):
        truth = edge_function(mask)
        values = [bool(mask & (1 << i)) for i in range(N)] + [False, True]
        for j, (op_and, a, b) in enumerate(gates):
            value = values[a] and values[b] if op_and else values[a] or values[b]
            values.append(value)
            if op_and and value and not truth:
                junk.add(j)
        if values[N + 2 + out] != truth:
            raise ValueError(f'decoded circuit disagrees on {mask}')
    if len(junk) < 2 or min(junk) != meta['first']:
        raise ValueError(f'decoded junk set disagrees: {junk}')
    print(json.dumps(dict(gates=gates, output_gate=out, junk=sorted(junk),
                          verified_assignments=1 << N), indent=2))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='cmd', required=True)
    a = sub.add_parser('encode')
    a.add_argument('out', type=Path)
    a.add_argument('--gates', type=int, default=21)
    a.add_argument('--first', type=int, default=10)
    b = sub.add_parser('decode')
    b.add_argument('meta', type=Path)
    b.add_argument('model', type=Path)
    args = parser.parse_args()
    if args.cmd == 'encode':
        encode(args.gates, args.first, args.out)
    else:
        decode(args.meta, args.model)
