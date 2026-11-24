"""Check the reduction on a constructed SAT instance and all inputs of its decoded model."""
import argparse
import itertools
import subprocess
import tempfile
from pathlib import Path
import json

from shard import EDGES, N, edge_function, extremal_rows, encode, decode


def run(cadical, ordered=False, normalize_aliases=False):
    maximal, edges = extremal_rows()
    for mask in range(1 << N):
        assert edge_function(mask) == any(mask & e == e for e in edges)
        assert edge_function(mask) == (not any(mask & independent == mask for independent in maximal))
    cover = next(c for c in itertools.combinations(range(N), 7)
                 if all(u in c or v in c for u, v in EDGES))
    stars = {p: [] for p in cover}
    for u, v in EDGES:
        if u in stars:
            stars[u].append(v)
        else:
            stars[v].append(u)
    gates = []
    def gate(op, a, b):
        if len(gates) == 10:
            # Deliberately unsafe, unused ANDs on the nonedge {0,1}.
            gates.extend([(True, 0, 0), (True, 0, 0)] if normalize_aliases
                         else [(True, 0, 1), (True, 0, 1)])
        gates.append((op, min(a, b), max(a, b)))
        return N + 2 + len(gates) - 1
    terms = []
    for p, neighbors in stars.items():
        assert neighbors
        cur = neighbors[0]
        for q in neighbors[1:]:
            cur = gate(False, cur, q)
        terms.append(gate(True, p, cur))
    cur = terms[0]
    for w in terms[1:]:
        cur = gate(False, cur, w)
    assert len(gates) == 24
    with tempfile.TemporaryDirectory() as tmp:
        cnf = Path(tmp) / 'known.cnf'
        encode(24, 10, cnf)
        meta_path = cnf.with_suffix('.json')
        meta = json.loads(meta_path.read_text())
        if ordered or normalize_aliases:
            from ordered_shard import normalize, extend
            augmented = Path(tmp) / 'ordered.cnf'
            extend(cnf, meta_path, augmented, normalize_aliases)
            gates, cur = normalize(gates, 10, cur, N+2)
            cnf = augmented
        pins = []
        for wire, (is_and, a, b) in zip(meta['gates'], gates):
            pins.extend([wire['left'][a], wire['right'][b], wire['op_and'] if is_and else -wire['op_and']])
        pins.append(meta['output'][cur-N-2])
        lines = cnf.read_text().splitlines()
        header = lines[0].split()
        lines[0] = f'p cnf {header[2]} {int(header[3])+len(pins)}' 
        cnf.write_text('\n'.join(lines + [f'{lit} 0' for lit in pins])+'\n')
        model = Path(tmp) / 'known.model'
        result = subprocess.run([cadical, '-q', '-w', str(model), str(cnf)], stdout=subprocess.PIPE)
        assert result.returncode == 10, result.stdout
        decode(meta_path, model)
    print('Extremal-row completeness, all 24 fixed gates, first junk position and 2048 decoded evaluations verified.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cadical')
    parser.add_argument('--ordered', action='store_true')
    parser.add_argument('--normalize-aliases', action='store_true')
    args = parser.parse_args()
    run(args.cadical, args.ordered, args.normalize_aliases)
