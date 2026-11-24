"""Exclude maximal isotropic level spaces of skew five-by-five matrices over F_p-bar.

Builds complete Grassmann charts for the centered or full skew slice and checks the quartic matching
polynomial on each. Requires SymPy and Singular 4.
"""

import argparse
from collections import Counter
from itertools import combinations, permutations, product
import subprocess

import sympy as sp


EDGES = list(combinations(range(5), 2))


def hyperbolic_pairs(prime, full):
    helmert = [sp.Matrix([1] * j + [-j] + [0] * (4-j)) for j in range(1, 5)]
    basis = [a*b.T - b*a.T for a,b in combinations(helmert, 2)]
    ones = sp.ones(5, 1)
    if full:
        basis.extend(ones*b.T - b*ones.T for b in helmert)

    def pairing(x, y):
        return sum(a*b for a,b in zip(x,y)) - 2*sum(a*b for a,b in zip(x*ones,y*ones))

    squared = [pairing(v, v) for v in basis]

    def pair_remaining(indices):
        if not indices:
            return []
        i = indices[0]
        for j in indices[1:]:
            root = next((k for k in range(1, prime)
                         if (squared[i]+k*k*squared[j]) % prime == 0), None)
            if root is None:
                continue
            rest = pair_remaining(tuple(s for s in indices if s not in (i,j)))
            if rest is not None:
                return [(i,j,root)] + rest
        return None

    matching = pair_remaining(tuple(range(len(basis))))
    if matching is None:
        raise ValueError("No hyperbolic pairing obtained with this basis and prime")
    pairs = [((basis[i]+k*basis[j]) % prime,
              ((basis[i]-k*basis[j])*pow(2*int(squared[i]), -1, prime)) % prime)
             for i,j,k in matching]
    flat = [v for pair in pairs for v in pair]
    for i,x in enumerate(flat):
        for j,y in enumerate(flat):
            assert pairing(x,y) % prime == int((i ^ 1) == j)
    return pairs


def quartic_terms():
    coefficients = Counter()
    for rows in combinations(range(5), 4):
        for columns in permutations(range(5), 4):
            entries = list(zip(rows, columns))
            if any(i == j for i, j in entries):
                continue
            monomial = tuple(sorted(EDGES.index((min(i, j), max(i, j))) for i, j in entries))
            coefficients[monomial] += (-1)**sum(i > j for i, j in entries)
    return '+'.join(str(c) + '*' + '*'.join(f'v[{j+1}]' for j in monomial)
                    for monomial, c in sorted(coefficients.items()) if c)


def chart_equations(mask, pairs, prime):
    count = len(pairs)
    variables = list(combinations(range(count), 2))
    first = [pair[(mask >> i) & 1] for i,pair in enumerate(pairs)]
    second = [pair[1-((mask >> i) & 1)] for i,pair in enumerate(pairs)]
    equations = []
    for sample in product(range(5), repeat=count-1):
        if sum(sample) > 4:
            continue
        x = (*sample, 1)
        entries = []
        for i,j in EDGES:
            constant = sum(x[k]*int(first[k][i,j]) for k in range(count)) % prime
            terms = [str(constant)]
            for q,(k,l) in enumerate(variables):
                value = (x[l]*int(second[k][i,j])-x[k]*int(second[l][i,j])) % prime
                if value:
                    terms.append(f'{value}*w{q}')
            entries.append('+'.join(terms))
        equations.append('r4(list('+','.join(entries)+'))')
    return equations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='include all row sums in the skew slice')
    parser.add_argument('--prime', type=int, choices=[7, 23, 29, 41, 61])
    parser.add_argument('--chart', type=int, help='run a single chart by its zero-based index')
    parser.add_argument('--singular', default='Singular')
    args = parser.parse_args()
    prime = args.prime or (29 if args.full else 61)
    pairs = hyperbolic_pairs(prime, args.full)
    chart_count = 2**len(pairs)
    charts = range(chart_count) if args.chart is None else [args.chart]
    if any(mask not in range(chart_count) for mask in charts):
        parser.error(f'chart index must lie between 0 and {chart_count-1}')
    variables = ','.join(f'w{j}' for j,_ in enumerate(combinations(pairs,2)))
    quartic = quartic_terms()
    for mask in charts:
        equations = chart_equations(mask, pairs, prime)
        program = [f'ring R={prime},({variables}),dp;',
                   'proc r4(list v){return('+quartic+');}',
                   'ideal I='+','.join(equations)+';',
                   'ideal B=slimgb(I);print(B[1]);print(size(B));quit;']
        result = subprocess.run([args.singular, '-q'], input='\n'.join(program)+'\n',
                                text=True, capture_output=True, check=True)
        if result.stderr or result.stdout.split() != ['1','1']:
            raise RuntimeError(f'Chart {mask}: '+result.stdout+result.stderr)
        if args.full:
            print(f'Chart {mask} has basis [1].', flush=True)
    print(f'Characteristic {prime}: all {len(charts)} selected chart ideals have basis [1].')


if __name__ == '__main__':
    main()
