"""Check that no four-dimensional skew level space is invariant under a nonidentity
simultaneous permutation of rows and columns. Requires SymPy and Singular 4.
"""

import argparse
from itertools import combinations, permutations, product
import subprocess

import sympy as sp

from check_centered_skew import EDGES, quartic_terms

ONES = sp.ones(5, 1)
UNITS = [sp.eye(5).col(j) for j in range(5)]
QUARTIC = quartic_terms()


def wedge(a, b):
    return a*b.T-b*a.T


def pairing(a, b):
    return sum(x*y for x,y in zip(a,b))-2*sum(x*y for x,y in zip(a*ONES,b*ONES))


def combo(matrices, scalars):
    return sum((v*m for v,m in zip(scalars,matrices)), sp.zeros(5))


def no_plane(gens, variables, prime, singular, test_quadratic):
    variables = variables or (sp.Symbol('unused'),)
    def encode(expr):
        return str(sp.Poly(expr, variables, modulus=prime).as_expr()).replace('**','^')
    equations = []
    if test_quadratic:
        for i,x in enumerate(gens):
            for y in gens[i:]:
                equations.append(encode(pairing(x,y)))
    for point in product(range(5), repeat=len(gens)-1):
        if sum(point) > 4:
            continue
        matrix = combo(gens, (*point,1))
        entries = [encode(matrix[i,j]) for i,j in EDGES]
        equations.append('r4(list('+','.join(entries)+'))')
    script = [f'ring R={prime},('+','.join(map(str,variables))+'),dp;',
              'proc r4(list v){return('+QUARTIC+');}',
              'ideal I='+','.join(equations)+';',
              'ideal B=slimgb(I); print(size(B));print(B[1]);quit;']
    res = subprocess.run([singular,'-q'], input='\n'.join(script)+'\n',
                         text=True, capture_output=True, check=True)
    if res.stderr or res.stdout.split()!=['1','1']:
        raise ArithmeticError(res.stdout+res.stderr)


def dual_basis(left, right, prime):
    gram = sp.Matrix([[pairing(a,b) for b in right] for a in left])
    inverse = gram.inv_mod(prime)
    return [combo(right, inverse.col(i)) % prime for i in range(len(left))]


def orthogonal_basis(vectors):
    work = vectors[:]
    result = []
    while work:
        i = next((j for j,v in enumerate(work) if pairing(v,v)), None)
        if i is None:
            i,j = next((i,j) for i,j in combinations(range(len(work)),2)
                       if pairing(work[i],work[j]))
            work[i] = work[i]+work[j]
        x = work.pop(i)
        work = [y-x*pairing(x,y)/pairing(x,x) for y in work]
        result.append(x*sp.ilcm(*(c.q for c in x)))
    return result


def max_isotropic_charts(matrices, prime):
    basis = orthogonal_basis(matrices)
    squared = [int(pairing(x,x)) % prime for x in basis]
    assert all(squared)
    for order in permutations(range(len(basis))):
        pairs = []
        for i,j in zip(order[::2],order[1::2]):
            k = next((k for k in range(1,prime) if (squared[i]+k*k*squared[j])%prime==0), None)
            if k is None:
                break
            pairs.append(((basis[i]+k*basis[j])%prime,
                          ((basis[i]-k*basis[j])*pow(2*squared[i],-1,prime))%prime))
        if 2*len(pairs)==len(basis):
            break
    else:
        raise ValueError('No hyperbolic pairing')
    flat = [v for pair in pairs for v in pair]
    assert all(pairing(a,b)%prime == int((i^1)==j)
               for i,a in enumerate(flat) for j,b in enumerate(flat))
    n = len(pairs)
    variables = sp.symbols('z:'+str(n*(n-1)//2))
    k = sp.zeros(n)
    for value,(i,j) in zip(variables, combinations(range(n),2)):
        k[i,j],k[j,i] = value,-value
    for mask in range(1 << n):
        first = [pair[(mask>>j)&1] for j,pair in enumerate(pairs)]
        second = [pair[1-((mask>>j)&1)] for j,pair in enumerate(pairs)]
        yield [x+combo(second,k.col(j)) for j,x in enumerate(first)], variables


def involutions(singular):
    charts = 0
    for double in (False,True):
        plus = [UNITS[0]+UNITS[1]]
        minus = [UNITS[0]-UNITS[1]]
        if double:
            plus.extend((UNITS[2]+UNITS[3],UNITS[4]))
            minus.append(UNITS[2]-UNITS[3])
        else:
            plus.extend(UNITS[2:])
        blocks = ([wedge(a,b) for part in (plus,minus) for a,b in combinations(part,2)],
                  [wedge(a,b) for a in plus for b in minus])
        for block in blocks:
            for gens,variables in max_isotropic_charts(block,241):
                no_plane(gens,variables,241,singular,False)
                charts += 1
    return charts


def three_cycle(singular):
    prime = 61
    w = pow(2,20,prime)
    fixed = [sum(UNITS[:3],sp.zeros(5,1)), *UNITS[3:]]
    p = sp.Matrix([1,w,w*w%prime,0,0])
    q = sp.Matrix([1,w*w%prime,w,0,0])
    zero = [wedge(a,b) for a,b in combinations(fixed,2)]+[wedge(p,q)]
    left = [wedge(a,p) for a in fixed]
    right = dual_basis(left,[wedge(a,q) for a in fixed],prime)
    charts = 0
    for pivots in combinations(range(4),2):
        rest = [i for i in range(4) if i not in pivots]
        y = sp.symbols('y:4')
        gens = [zero[k]+combo([zero[i] for i in rest],y[2*j:2*j+2])
                for j,k in enumerate(pivots)]
        no_plane(gens,y,prime,singular,True)
        charts += 1
    for i in range(4):
        x = sp.symbols('x:3')
        fixed_line = zero[i]+combo([z for j,z in enumerate(zero) if j!=i], x)
        no_plane([fixed_line,*left],x,prime,singular,True)
        charts += 1
        for j in range(3):
            y = sp.symbols('y:2')
            other = [k for k in range(3) if k!=j]
            gens = [fixed_line, *[left[k]-c*left[j] for k,c in zip(other,y)],
                    right[j]+combo([right[k] for k in other],y)]
            no_plane(gens,(*x,*y),prime,singular,True)
            charts += 1
    return charts


def five_cycle(singular):
    prime = 61
    w = pow(2,12,prime)
    chars = [sp.Matrix([pow(w,a*j,prime) for j in range(5)]) for a in range(5)]
    spaces = [[] for _ in range(5)]
    for a,b in combinations(range(5),2):
        spaces[(a+b)%5].append(wedge(chars[a],chars[b])%prime)
    zero,left1,left2,right2,right1 = spaces
    def opposite_choices(left,right,var):
        right = dual_basis(left,right,prime)
        t = sp.Symbol(var)
        result = [((),[])]
        for side in (left,right):
            result.extend([((t,),[side[0]+t*side[1]]),((),[side[1]]),((),side)])
        result.extend([((t,),[left[0]+t*left[1],right[1]-t*right[0]]),
                       ((),[left[1],right[0]])])
        return result
    fixed_options = [[]]
    assert pairing(zero[1],zero[1]) % prime
    for n in range(prime):
        z = (zero[0]+n*zero[1]) % prime
        if pairing(z,z)%prime==0:
            fixed_options.append([z])
    assert len(fixed_options)==3
    charts = 0
    for (a,left),(b,right),z in product(opposite_choices(left1,right1,'a'),
                                        opposite_choices(left2,right2,'b'),fixed_options):
        gens = left+right+z
        if len(gens)==4:
            no_plane(gens,a+b,prime,singular,False)
            charts += 1
    return charts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular',default='Singular')
    args = parser.parse_args()
    for fn in (involutions,three_cycle,five_cycle):
        print(f'{fn.__name__}: {fn(args.singular)} chart ideals equal [1].',flush=True)
