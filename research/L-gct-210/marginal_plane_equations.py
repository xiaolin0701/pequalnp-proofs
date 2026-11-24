"""Print a single Grassmannian chart testing complex additive marginal planes.

Input for msolve, over a prime field of characteristic greater than five.
Permuting row coordinates covers all charts, since the row projection injects.
"""

import argparse

from sympy.polys.domains import GF
from sympy.polys.rings import ring


def add(left, right):
    return [x+y for x, y in zip(left, right)]


def mul(left, right, zero):
    result = [zero for _ in range(len(left)+len(right)-1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] = result[i+j]+a*b
    return result


def elementary(linear, polynomials):
    zero = polynomials.zero
    values = [[polynomials.one]]+[[zero]*(k+1) for k in range(1, 6)]
    for i, factor in enumerate(linear):
        for k in range(i+1, 0, -1):
            values[k] = add(values[k], mul(values[k-1], factor, zero))
    return values


def terms(poly, names, prime):
    pieces = []
    for powers, coefficient in poly.terms():
        factors = [str(int(coefficient) % prime)]
        for name, power in zip(names, powers):
            if power:
                factors.append(name if power == 1 else f'{name}^{power}')
        pieces.append('*'.join(factors))
    return '+'.join(pieces) or '0'


def equations(prime):
    names = [f'x{i}' for i in range(12)]
    polynomials, *x = ring(','.join(names), GF(prime))
    zero, one = polynomials.zero, polynomials.one
    rows = [(one,zero),(zero,one),x[0:2],x[2:4]]
    cols = [x[i:i+2] for i in range(4, 12, 2)]
    for group in (rows, cols):
        group.append(tuple(-sum(entries, zero) for entries in zip(*group)))
    b,c = [elementary(group, polynomials) for group in (rows,cols)]
    quartic = mul(b[2], b[2], zero)
    quintic = mul(b[2], b[3], zero)
    forms = [*add(b[2], c[2]), *add(b[3], c[3]),
             *(10*(f+g)-3*h for f,g,h in zip(b[4], c[4], quartic)),
             *(5*(f+g)-h for f,g,h in zip(b[5], c[5], quintic))]
    assert len(forms) == 18
    print(','.join(names))
    print(prime)
    print(',\n'.join(terms(form, names, prime) for form in forms))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('prime', type=int)
    args = parser.parse_args()
    if args.prime < 7 or any(args.prime % i == 0 for i in range(2,int(args.prime**0.5)+1)):
        parser.error('the characteristic must be prime and greater than five')
    equations(args.prime)
