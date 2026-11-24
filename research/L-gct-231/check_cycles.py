"""Generate exact Singular tests for symmetric 4 by 4 level planes stabilized by a 3- or 4-cycle."""

import argparse
import itertools
from math import prod

from sympy.polys.domains import GF
from sympy.polys.rings import ring


def substitutions(size, names):
    for pivot in range(size):
        yield [f'{v}={int(i == pivot)}' for i, v in enumerate(names[:pivot+1])]


def format_poly(poly, names, prime):
    terms = []
    for exponents, coeff in poly.terms():
        factors = [str(int(coeff) % prime)]
        for e, name in zip(exponents, names):
            if e:
                factors.append(name if e == 1 else f'{name}^{e}')
        terms.append('*'.join(factors))
    return '+'.join(terms) or '0'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cycle', type=int, choices=[3, 4])
    args = parser.parse_args()
    n = args.cycle
    p, root = (7, 2) if n == 3 else (13, 5)
    names = ['a0', 'b0', 'c0', 'a1', 'b1', 'c1', 'a2', 'b2', 'c2', 'a3', 'b3']
    tags = ['t0', 't1', 't2', 't3']
    polynomials, *variables = ring(','.join(names+tags), GF(p))
    v = dict(zip(names+tags, variables))
    m = [[polynomials.zero for _ in range(4)] for _ in range(4)]
    for k in range(n):
        a, b, t = v[f'a{k}'], v[f'b{k}'], v[f't{k}']
        for i in range(n):
            z = pow(root, i*k, p)
            m[i][i] += a*z*t
            j = (i+1) % n
            m[i][j] += b*z*t
            m[j][i] += b*z*t
        if n == 3:
            c = v[f'c{k}']
            for i in range(3):
                m[i][3] += c*pow(root, i*k, p)*t
                m[3][i] += c*pow(root, i*k, p)*t
            if k == 0:
                m[3][3] = (-3*a-6*b-6*c)*t
        elif k % 2 == 0:
            c = -a-2*b if k == 0 else v[f'c{k}']
            for i in range(2):
                m[i][i+2] += c*pow(root, i*k, p)*t
                m[i+2][i] += c*pow(root, i*k, p)*t
    forms = {}
    for degree in range(2, 5):
        total = sum((prod((m[i][j] for i,j in zip(rows,cols)), start=polynomials.one)
                     for rows in itertools.combinations(range(4),degree)
                     for cols in itertools.permutations(range(4),degree)), polynomials.zero)
        for exponents, coeff in total.terms():
            tag = exponents[len(names):]
            base = polynomials.from_dict({(*exponents[:len(names)],0,0,0,0):coeff})
            forms[tag] = forms.get(tag,polynomials.zero)+base

    def output(name, forms_to_use, variables_to_use, smooth=False, pivots=()):
        print(f'ring {name}={p},({",".join(variables_to_use)}),dp;')
        strings = [format_poly(poly,names,p) for poly in forms_to_use]
        if smooth:
            print('poly curve='+strings[0]+'; ideal J=jacob(curve);')
        else:
            print('ideal J='+','.join(strings)+';')
        if not pivots:
            print(f'print("{name} homogeneous affine dimension"); dim(std(J));')
        else:
            print('ideal chartIdeal;')
            for chart in itertools.product(*[list(substitutions(len(group),group)) for group in pivots]):
                fixes = [equation.replace('=','-') for group in chart for equation in group]
                print('chartIdeal=J,'+','.join(fixes)+'; if (reduce(1,std(chartIdeal))!=0) { ERROR("nonempty chart"); }')
            print(f'print("{name} all affine charts empty");')

    def pure(k):
        return [f for tag,f in forms.items() if tag[k]==sum(tag)]
    output('fixed',pure(0),names[:3] if n == 3 else names[:2])
    if n == 3:
        output('weightOneJacobian',pure(1),names[3:6],smooth=True)
        output('weightTwoJacobian',pure(2),names[6:9],smooth=True)
    else:
        for k, group in ((1,['a1','b1']),(3,['a3','b3'])):
            quartic=pure(k)[0]
            assert quartic
            print(f'// Weight {k} has a nonzero quartic: '+format_poly(quartic,names,p))
        q2 = next(f for tag,f in forms.items() if tag==(0,0,2,0))
        output('weightTwoJacobian',[q2],names[6:9],smooth=True)
        groups = [['a1','b1'],['a2','b2','c2'],['a3','b3']]
        output('mixed',[f for tag,f in forms.items() if tag[0]==0],sum(groups,[]),pivots=groups)
    print('quit;')


if __name__ == '__main__':
    main()
