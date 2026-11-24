"""Test coplanarity at the exceptional fifth-root scales over the rationals."""

import argparse
from itertools import combinations
from pathlib import Path
import shutil
import subprocess
import tempfile

from flint import fmpz_mpoly, fmpz_mpoly_ctx

NAMES = ('A', 'B', 'C', 'D', 'E', 'g', 'k', 'r', 't')


def endpoint_system(singular, key):
    relations = {'unit': 't+1', 'scale': '24*t^5-1', 'diag': '2*t^2-t+2',
                 'off': '1+t*(1+r)-4*t^2*r'}
    missing = {'diag': '(i==1 && j==1)', 'off': '(i==1 && j==2)'}.get(key, '(0)')
    source = f"""
        ring R=(0,r),(t,A,B,C,D,E,g,k),dp; minpoly=r^4+r^3+r^2+r+1;
        poly rel={relations[key]}; ideal Q=std(rel);
        matrix Dn[5][5]; matrix H[5][5]; matrix M[5][4];
        int i,j; poly whole=1; poly cond=0; poly numeratorterm; poly cofac;
        for(i=1;i<=5;i++){{for(j=i;j<=5;j++){{
            Dn[i,j]=1+t*(r^(i-1)+r^(j-1))-4*t^2*r^(i+j-2);
            if(i==j){{Dn[i,j]=Dn[i,j]-5;}}
            if{missing}{{cond=r^(i-1)*var(j+1)+r^(j-1)*var(i+1);}}
            else{{whole=whole*Dn[i,j];}}
        }}}}
        for(i=1;i<=5;i++){{for(j=i;j<=5;j++){{
            if{missing}{{H[i,j]=reduce(whole*g,Q);}}
            else{{
                cofac=whole/Dn[i,j]; numeratorterm=r^(i-1)*var(j+1)+r^(j-1)*var(i+1);
                H[i,j]=reduce(cofac*numeratorterm,Q);
            }}
            H[j,i]=H[i,j];
        }}}}
        for(i=1;i<=5;i++){{for(j=1;j<=4;j++){{M[i,j]=H[i,j]-H[i,5];}}}}
        ideal minors=minor(M,3); minors=reduce(minors,Q); ideal base=rel,cond,minors;
        ring Z=0,(A,B,C,D,E,g,k,r,t),dp;
        ideal finalJ=imap(R,base),r^4+r^3+r^2+r+1;
        short=0; for(int m=1;m<=ncols(finalJ);m++){{
            if(finalJ[m]!=0){{string(cleardenom(finalJ[m]));}}
        }} quit;
    """
    run = subprocess.run([singular, '-q'], input=source, capture_output=True,
                         text=True, check=True)
    ring = fmpz_mpoly_ctx.get(NAMES)
    equations = []
    for line in run.stdout.splitlines():
        if '?' in line or line.startswith('//'):
            raise RuntimeError(line)
        expr = fmpz_mpoly(line, ring)
        expr = expr // expr.content()
        if expr not in equations and -expr not in equations:
            equations.append(expr)
    assert equations
    return ring, equations


def saturated_system(ring, equations, key, i, j):
    values = list(ring.gens())
    values[i] = ring.constant(1)
    if key == 'unit':
        values[8] = ring.constant(-1)
    if key in ('unit', 'scale'):
        values[5] = ring.constant(0)
    specialized = [poly.compose(*values) for poly in equations]
    specialized.append(values[6]*values[j]-1)
    keep = [k for k in range(len(NAMES)) if values[k] in ring.gens()]
    names = [NAMES[k] for k in keep]
    smaller = fmpz_mpoly_ctx.get(tuple(names))
    substitution = [smaller.gens()[keep.index(k)] if k in keep else smaller.constant(0)
                    for k in range(len(NAMES))]
    polys = []
    for poly in specialized:
        if poly:
            expr = poly.compose(*substitution)
            expr = expr // expr.content()
            if expr not in polys and -expr not in polys:
                polys.append(expr)
    return ','.join(names) + '\n0\n' + ',\n'.join(str(f).replace(' ', '') for f in polys) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular', default=shutil.which('Singular') or 'Singular')
    parser.add_argument('--msolve', default=shutil.which('msolve') or 'msolve')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as folder:
        source = Path(folder) / 'system.in'
        output = Path(folder) / 'solution.out'
        for key in ('unit', 'diag', 'off'):
            ring, equations = endpoint_system(args.singular, key)
            for i, j in combinations(range(5), 2):
                source.write_text(saturated_system(ring, equations, key, i, j))
                output.unlink(missing_ok=True)
                subprocess.run([args.msolve, '-t', '2', '-f', str(source), '-o', str(output)],
                               check=True, capture_output=True)
                assert output.read_text().strip() == '[-1]:', (key, i, j)
            print(f'{key}: all ten support charts have unit ideal', flush=True)


if __name__ == '__main__':
    main()
