"""Exact bounded synthesis for the Petersen-minus-a-vertex shard starting with NOT x4."""
import argparse
import itertools
import json
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / 'L-meta-1343'))
from shard import Encoding

EDGES = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))


def target(mask):
    return any(mask >> i & mask >> j & 1 for i,j in EDGES)


def evaluate(gates, mask):
    wires = [bool(mask >> i & 1) for i in range(9)]
    for op, i, j in gates:
        a, b = wires[i], wires[j]
        wires.append((not a) if op == 'not' else ((a and b) if op == 'and' else (a or b)))
    return wires[-1]


def encode(count, path, witness=None):
    cnf = Encoding()
    rows = [[bool(mask >> i & 1) for i in range(9)] + [not bool(mask >> 4 & 1)]
            for mask in range(512)]
    info = []
    for k in range(1,count):
        width = k+9
        left, right = cnf.one(width), cnf.one(width)
        op = cnf.one(3)
        for i in range(width):
            for j in range(i):
                cnf.add(-left[i],-right[j])
            cnf.add(-op[2],-left[i],right[i])
        if witness:
            kind,i,j = witness[k]
            cnf.add(op[['and','or','not'].index(kind)])
            cnf.add(left[i]); cnf.add(right[j])
        for row in rows:
            a, b = cnf.mux(left,row), cnf.mux(right,row)
            z = cnf.new()
            for cond, clauses in zip(op, [((-z,a),(-z,b),(z,-a,-b)),
                                          ((z,-a),(z,-b),(-z,a,b)),
                                          ((-z,-a),(z,a))]):
                for clause in clauses:
                    cnf.add(-cond,*clause)
            row.append(z)
        info.append(dict(left=left,right=right,op=op))
    for mask,row in enumerate(rows):
        cnf.add(row[-1] if target(mask) else -row[-1])
    # Sort the free suffix. An adjacent inversion of (right,left,op) cannot
    # be a dependency, so its two gates commute. NOT encodes its input twice.
    for a,b in zip(info,info[1:]):
        ties = []
        for key in ('right','left','op'):
            for i,sel in enumerate(a[key]):
                for prev in b[key][:i]:
                    cnf.add(*[-t for t in ties], -sel, -prev)
            if key != 'op':
                tie = cnf.new()
                for x,y in zip(a[key],b[key]):
                    cnf.add(-x,-y,tie)
                ties.append(tie)
    cnf.dimacs(path)
    path.with_suffix('.json').write_text(json.dumps(info))


def decode(path, model):
    positive = {int(v) for line in model.read_text().splitlines() if line.startswith('v ')
                for v in line.split()[1:] if int(v)>0}
    def choose(xs):
        chosen = [k for k,v in enumerate(xs) if v in positive]
        assert len(chosen)==1
        return chosen[0]
    gates = [('not',4,4)]
    for g in json.loads(path.read_text()):
        gates.append((['and','or','not'][choose(g['op'])], choose(g['left']), choose(g['right'])))
    assert all(target(mask)==evaluate(gates,mask) for mask in range(512))
    print(json.dumps(gates))


def example():
    gates = [('not',4,4)]
    def add(op,a,b):
        gates.append((op,min(a,b),max(a,b)))
        return 8+len(gates)
    def fold(op, xs):
        z,*tail=xs
        for q in tail:z=add(op,z,q)
        return z
    cover = next(s for s in itertools.combinations(range(9),5) if all(i in s or j in s for i,j in EDGES))
    neighbors = {s:[] for s in cover}
    for a,b in EDGES:
        i,j=(a,b) if a in neighbors else (b,a)
        neighbors[i].append(j)
    products = [add('and',i,fold('or',js)) for i,js in neighbors.items() if js]
    fold('or',products)
    assert len(gates)==17 and all(target(m)==evaluate(gates,m) for m in range(512))
    # Use the same suffix normal form as the actual bounded search.
    def key(g):
        op, i, j = g
        return j, i, ['and','or','not'].index(op)
    while True:
        k = next((i for i in range(1,len(gates)-1) if key(gates[i])>key(gates[i+1])), None)
        if k is None:
            break
        wire = 9+k
        assert gates[k+1][2]<wire
        gates[k],gates[k+1] = gates[k+1],gates[k]
        def rename(i):
            if i==wire: return wire+1
            if i==wire+1: return wire
            return i
        for h in range(k+2,len(gates)):
            op,i,j=gates[h]
            i,j=sorted((rename(i),rename(j)))
            gates[h]=(op,i,j)
    assert all(target(m)==evaluate(gates,m) for m in range(512))
    return gates


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('encode','witness','decode'))
    parser.add_argument('path',type=Path)
    parser.add_argument('model',nargs='?',type=Path)
    args=parser.parse_args()
    if args.mode=='decode':
        decode(args.path,args.model)
    elif args.mode=='witness':
        encode(17,args.path,example())
    else:
        encode(15,args.path)
