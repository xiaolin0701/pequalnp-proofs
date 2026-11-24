"""Classify the e2=e3 lines over Q, then reject the relevant five-line tuples mod 101."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod
from random import Random

import sympy as sp


def verify_fano_chart():
    parameters = sp.symbols("a b c d e f")
    a, b, c, d, e, f = parameters
    x, y = sp.symbols("x y")
    forms = [x, y, a*x+b*y, c*x+d*y, e*x+f*y]
    equations = []
    for degree in (2, 3):
        poly = sum(sp.prod(term) for term in combinations(forms, degree))
        equations.extend(sp.Poly(poly, x, y).coeffs())
    basis = sp.groebner(equations, *parameters, order="grevlex", domain=sp.QQ)
    leading = [poly.LM(order=basis.order).exponents for poly in basis.polys]
    limits = [min(m[i] for m in leading if m[i] and sum(m)==m[i]) for i in range(6)]
    quotient_dimension = sum(
        all(any(x<y for x,y in zip(power,lm)) for lm in leading)
        for power in product(*(range(n) for n in limits))
    )
    assert quotient_dimension == 12
    print("Q chart quotient dimension:", quotient_dimension)


prime = 101


def row_reduce(rows):
    work = [list(row) for row in rows]
    pivots = []
    for j in range(len(work[0])):
        level = len(pivots)
        k = next((k for k in range(level,len(work)) if work[k][j]%prime), None)
        if k is None:
            continue
        work[level],work[k] = work[k],work[level]
        inv = pow(work[level][j]%prime, -1, prime)
        work[level] = [v*inv%prime for v in work[level]]
        for i,row in enumerate(work):
            if i != level and row[j]%prime:
                work[i] = [(x-row[j]*y)%prime for x,y in zip(row,work[level])]
        pivots.append(j)
        if len(pivots)==len(work):
            break
    return tuple(tuple(r) for r in work[:len(pivots)]),pivots


def nullspace(rows):
    reduced,pivots = row_reduce(rows)
    result = []
    for j in range(len(rows[0])):
        if j in pivots:
            continue
        vec = [0]*len(rows[0])
        vec[j] = 1
        for k,index in enumerate(pivots):
            vec[index] = -reduced[k][j]%prime
        result.append(vec)
    return result


def list_lines():
    # Fourth roots modulo 101. Fix the first nonzero entry of the second
    # generator to 1, leaving the other three unordered values to permute.
    assert 10**2 % prime == prime-1
    lines = []
    for center in range(5):
        axis = tuple(int(j==center) for j in range(5))
        for rest in permutations([10,100,91]):
            iterator = iter((1,*rest))
            second = tuple(0 if j==center else next(iterator) for j in range(5))
            lines.append((axis,second))
    assert len(lines)==30
    return lines


def verify_five_lines():
    lines = list_lines()
    hyperplanes = {}
    for i,j in combinations(range(30),2):
        head,_ = row_reduce(lines[i]+lines[j])
        if len(head)==4 and head not in hyperplanes:
            hyperplanes[head] = [k for k,line in enumerate(lines)
                                 if len(row_reduce(head+line)[0])==4]
    assert Counter(map(len,hyperplanes.values())) == {4:60,6:30}
    permutations5 = tuple(permutations(range(5)))
    rng = Random(314159)
    checked = Counter()
    for contained in hyperplanes.values():
        for indices in combinations_with_replacement(contained,5):
            counts = tuple(sorted(Counter(indices).values()))
            if counts not in ((1,1,1,1,1),(1,2,2)):
                continue
            vectors = sum((lines[i] for i in indices),())
            if len(row_reduce(vectors)[0]) != 4:
                continue
            relations = nullspace(list(zip(*vectors)))
            found = False
            for _ in range(12):
                weights = [rng.randrange(prime) for _ in relations]
                coeff = [sum(a*b for a,b in zip(col,weights))%prime
                         for col in zip(*relations)]
                matrix = [[1+coeff[2*i]*vectors[2*i][j]+coeff[2*i+1]*vectors[2*i+1][j]
                           for j in range(5)] for i in range(5)]
                assert all(sum(matrix[i][j]-1 for i in range(5))%prime==0 for j in range(5))
                permanent = sum(prod(matrix[i][s[i]] for i in range(5)) for s in permutations5)
                if (permanent-120)%prime:
                    found = True
                    break
            assert found, indices
            checked[counts] += 1
    assert checked == {(1,1,1,1,1):180,(1,2,2):2520}
    print("Four-spaces with four/six lines:", 60,30)
    print("Five distinct lines / multiplicities 2+2+1, all with witnesses:",
          checked[(1,1,1,1,1)],checked[(1,2,2)])


if __name__ == "__main__":
    verify_fano_chart()
    verify_five_lines()
