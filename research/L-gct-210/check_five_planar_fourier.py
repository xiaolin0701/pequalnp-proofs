"""Locate every scale at which coplanarity cubics fail to span the axis ideal."""

import argparse
from itertools import combinations, combinations_with_replacement
from math import factorial, gcd
from random import Random
import shutil
import subprocess

from flint import fmpq_poly, fmpz_mat, fmpz_mpoly, fmpz_mpoly_ctx, fmpz_poly, nmod_mat


def coefficients(singular):
    source = ["""
        ring R=(0,r),(t,x0,x1,x2,x3,x4),(dp(1),dp(5));
        minpoly=r^4+r^3+r^2+r+1;
        matrix W[5][5]; matrix H[5][5]; matrix D[5][4]; matrix lam[5][1];
        int i,j,k,l; poly a,b,prodrow; poly diagonal=1; poly off=1;
        for(i=1;i<=5;i++){
            for(j=1;j<=5;j++){
                a=r^(i-1); b=r^(j-1); W[i,j]=1+t*(a+b)-4*t^2*a*b;
                if(i==j){W[i,j]=W[i,j]-5; diagonal=diagonal*W[i,j];}
                if(i<j){off=off*W[i,j];}
            }
            for(j=0;j<5;j++){lam[i,1]=lam[i,1]+r^((i-1)*j)*var(j+2);}
        }
        if(diagonal!=-32*(32*t^10-61*t^5+32)){ERROR("diagonal norm");}
        if(off!=1048576*t^20+175104*t^15-14269*t^10-171*t^5+1){ERROR("off-diagonal norm");}
        for(i=1;i<=5;i++){for(j=1;j<=5;j++){
            prodrow=1;
            for(k=1;k<=5;k++){if(k!=j){prodrow=prodrow*W[i,k];}}
            H[i,j]=prodrow*(r^(j-1)*lam[i,1]+r^(i-1)*lam[j,1]);
        }}
        for(i=0;i<5;i++){for(j=1;j<=4;j++){
            for(k=1;k<=5;k++){for(l=1;l<=5;l++){
                D[i+1,j]=D[i+1,j]+r^((k-1)*i+(l-1)*j)*H[k,l];
            }}
        }}
        matrix M[3][3]; poly cubic; poly coefficient; short=0;
    """]
    for rows in combinations(range(1, 6), 3):
        for cols in combinations(range(1, 5), 3):
            for i, row in enumerate(rows, 1):
                for j, col in enumerate(cols, 1):
                    source.append(f'M[{i},{j}]=D[{row},{col}];')
            source.append('cubic=det(M);')
            for triple in combinations_with_replacement(range(5), 3):
                term = 'cubic'
                denominator = 1
                for k in triple:
                    term = f'diff({term},x{k})'
                for k in set(triple):
                    denominator *= factorial(triple.count(k))
                source.append(f'coefficient={term}/{denominator};string(coefficient);')
    source.append('quit;')
    result = subprocess.run([singular, '-q'], input='\n'.join(source), text=True,
                            capture_output=True, check=True)
    lines = result.stdout.splitlines()
    if len(lines) != 40 * 35:
        raise ValueError((lines[:5], result.stderr))
    ring = fmpz_mpoly_ctx.get(('t',))
    entries = []
    for line in lines:
        expr = fmpz_mpoly(line, ring)
        coeffs = [0] * (max(expr.degrees()[0], 0) + 1)
        for (i,), value in expr.to_dict().items():
            coeffs[i] = value
        entries.append(fmpz_poly(coeffs))
    return [entries[i:i+35] for i in range(0, len(entries), 35)]


def pivots(matrix):
    echelon, rank = matrix.rref()
    return [next(j for j in range(echelon.ncols()) if echelon[i, j]) for i in range(rank)]


def residue(poly):
    powers = {i % 5 for i, a in enumerate(poly) if a}
    assert len(powers) <= 1
    return next(iter(powers), None)


def compressed_minor(matrix):
    # Factor from each row and column a monomial in t. The remaining entries
    # are univariate in y=t^5. Additional powers of y are units on the chart.
    n = len(matrix)
    col = next(j for j in range(n) if all(row[j] for row in matrix))
    row_shifts = [residue(row[col]) for row in matrix]
    col_shifts = []
    for j in range(n):
        terms = {(residue(row[j]) - row_shifts[i]) % 5
                 for i, row in enumerate(matrix) if row[j]}
        assert len(terms) == 1
        col_shifts.append(terms.pop())
    result = []
    for i, row in enumerate(matrix):
        converted = []
        for j, poly in enumerate(row):
            coeffs = [0] * (3 + max(0, poly.degree()) // 5)
            for k, a in enumerate(poly):
                if a:
                    power, rem = divmod(k-row_shifts[i]-col_shifts[j], 5)
                    assert rem == 0 and power + 2 >= 0
                    coeffs[power+2] = a
            converted.append(fmpz_poly(coeffs))
        content = gcd(*(int(f.content()) for f in converted))
        result.append([f // content for f in converted])
    return result


def determinant(matrix):
    bound = sum(max(f.degree() for f in row) for row in matrix)
    values = [fmpz_mat([[f(i) for f in row] for row in matrix]).det()
              for i in range(bound+1)]
    expr = fmpq_poly()
    binomial = fmpq_poly([1])
    variable = fmpq_poly([0, 1])
    for i in range(bound+1):
        expr += values[0] * binomial
        values = [b-a for a, b in zip(values, values[1:])]
        binomial = binomial * (variable-i) / (i+1)
    assert all(a.q == 1 for a in expr)
    integer = fmpz_poly([int(a) for a in expr])
    assert integer
    return integer // integer.content()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular', default=shutil.which('Singular') or 'Singular')
    args = parser.parse_args()
    coeffs = coefficients(args.singular)
    numeric = [[int(f(1)) % 101 for f in row] for row in coeffs]
    common = None
    for seed in range(5):
        order = list(range(40))
        Random(seed).shuffle(order)
        reduced = nmod_mat([numeric[i] for i in order], 101)
        rows = [order[i] for i in pivots(reduced.transpose())]
        cols = pivots(reduced)
        assert len(rows) == len(cols) == 30
        minor = [[coeffs[i][j] for j in cols] for i in rows]
        pol = determinant(compressed_minor(minor))
        common = pol if common is None else common.gcd(pol)
        print(f'Exact minor {seed+1}, degree {pol.degree()}, gcd degree {common.degree()}', flush=True)
    y = fmpz_poly([0, 1])
    expected = (y**43 * (y+1)**4 * (24*y-1)**10 * (32*y**2-61*y+32)**4
                * (1048576*y**4+175104*y**3-14269*y**2-171*y+1)**15)
    assert common == expected or common == -expected
    print('Only the two denominator norms, y=0, y=-1, and 24y=1 are exceptional.')


if __name__ == '__main__':
    main()
