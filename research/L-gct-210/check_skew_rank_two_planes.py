"""Classify all three-dimensional skew level spaces of matrices of rank at most two.

Requires SymPy and Singular. The center classification and the common three-space
test run in characteristic zero. Extension tests run on the projective fiber at 31.
"""

import argparse
from itertools import combinations, product
import subprocess

import sympy as sp
from sympy.polys.matrices import DomainMatrix
from check_centered_skew import EDGES, quartic_terms


def simplex(dimension):
    return [u for u in product(range(5), repeat=dimension) if sum(u) <= 4]


def expression(x):
    return '(' + str(x).replace('**', '^') + ')'


def wedge(a, b):
    return sp.Matrix([a[i]*b[j] - a[j]*b[i] for i, j in EDGES])


def quartic(entries):
    return 'r4(list(' + ','.join(map(expression, entries)) + '))'


def check(singular, prime, variables, equations, command, expected):
    script = [f'ring R={prime},(' + ','.join(map(str, variables)) + '),dp;',
              'proc r4(list v){return(' + quartic_terms() + ');}',
              'ideal I=' + ','.join(equations) + ';', command, 'quit;']
    result = subprocess.run([singular, '-q'], input='\n'.join(script) + '\n',
                            text=True, capture_output=True, check=True)
    if result.stderr or result.stdout.split() != expected:
        raise ArithmeticError(result.stdout + result.stderr)


def centers(singular):
    x = sp.symbols('x:4')
    f = sp.Matrix([1, *x])
    a = 4*f - sp.ones(5, 1)*sum(f)
    equations = [expression(a.dot(f))]
    for u in simplex(3):
        tail = sp.Matrix([*u, 1])
        b = sp.Matrix([-sp.Matrix(x).dot(tail), *tail])
        equations.append(quartic(wedge(a, b)))
    check(singular, 0, x, equations,
          'LIB "primdec.lib"; ideal G=std(radical(std(I)));print(dim(G));print(vdim(G));',
          ['0', '16'])
    # Suffices to verify the two projective permutation orbits in characteristic zero.
    w = sp.Symbol('w')
    for a in (sp.Matrix([1, 0, 0, 0, 0]), sp.Matrix([1, w, -1-w, 0, 0])):
        f = a - sp.ones(5, 1)*sum(a)
        pivot = next(i for i in range(5) if f[i] == 1 or f[i] == -1)
        E = sp.eye(5)
        B = [f[pivot]*E.col(j) - f[j]*E.col(pivot) for j in range(5) if j != pivot]
        polys = [expression(a.dot(f))]
        for u in simplex(3):
            b = sp.Matrix.hstack(*B)*sp.Matrix([*u, 1])
            polys.append(quartic(wedge(a, b)))
        check(singular, 0, [w], polys,
              'ideal H=std(w^2+w+1);print(size(simplify(reduce(I,H),2)));', ['0'])


def three_space(singular):
    x = sp.symbols('x:6')
    f, g = sp.Matrix([1, 0, *x[:3]]), sp.Matrix([0, 1, *x[3:]])
    equations = [expression(4*a.dot(b)-sum(a)*sum(b)) for a,b in ((f,f),(f,g),(g,g))]
    B = [sp.Matrix([-f[j], -g[j], *sp.eye(3).col(j-2)]) for j in range(2, 5)]
    G = sp.Matrix.hstack(*(wedge(a,b) for a,b in combinations(B, 2)))
    equations.extend(quartic(G*sp.Matrix([*u, 1])) for u in simplex(2))
    check(singular, 0, x, equations, 'ideal G=slimgb(I);print(size(G));print(G[1]);',
          ['1', '1'])


def finite_matrix(A):
    return DomainMatrix.from_Matrix(A).convert_to(sp.GF(31))


def null(A):
    return finite_matrix(A).nullspace().to_Matrix().T


def independent(A):
    return list(finite_matrix(A).rref()[1])


def extensions(singular):
    p = 31
    incidence = sp.zeros(5, 10)
    for k,(i,j) in enumerate(EDGES):
        incidence[i,k], incidence[j,k] = 1, -1
    metric = sp.eye(10)-incidence.T*incidence
    assert (5**2+5+1) % p == 0
    for a in (sp.Matrix([1,0,0,0,0]), sp.Matrix([1,5,25,0,0])):
        f = a-sp.ones(5,1)*sum(a)
        B = null(f.T)
        S = sp.Matrix.hstack(*(wedge(a,b) for b in B.columnspace()))
        S = S[:,independent(S)]
        assert S.cols == 3 and (S.T*metric*S) % p == sp.zeros(3)
        all_directions = S.row_join(null(S.T*metric))
        independent_columns = independent(all_directions)
        assert independent_columns[:3] == [0,1,2] and len(independent_columns) == 7
        H = all_directions[:,independent_columns[3:]]
        vars = sp.symbols('x:3')
        for k in range(4):
            Z = H*sp.Matrix([0]*k+[1]+list(vars[:3-k]))
            equations = [expression((Z.T*metric*Z)[0])]
            equations.extend(quartic(Z+S*sp.Matrix(u)) for u in simplex(3))
            check(singular, p, vars, equations, 'ideal G=slimgb(I);print(size(G));print(G[1]);',
                  ['1','1'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular', default='Singular')
    args = parser.parse_args()
    for method in (centers, three_space, extensions):
        method(args.singular)
        print(method.__name__, 'verified', flush=True)
