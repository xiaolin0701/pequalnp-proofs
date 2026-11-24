"""Finite certificate for the simultaneous five-cycle on rows and columns.

Python standard library and Singular 4. Run with --singular PATH if needed.
Every five-by-five complex level space invariant under the simultaneous
cyclic shift of rows and columns has dimension <= 8. If its invariant part
has positive dimension, its total dimension is <= 7.

Reduction at 311 is legitimate for this nonexistence test. Such a d-plane
is a point of the Grassmannian of d-planes in 25-space, cut out by closed
conditions (shift-invariance and vanishing of all positive-degree restricted
coefficients of per(J+T)). This is projective over Z. If the characteristic
zero fiber is nonempty, its closed image contains the generic point of
Spec Z and hence also the fiber at 311 after algebraic closure. The same
argument for the bound with a nonzero fixed part uses the flag variety of a
fixed line inside L. The proof below rules out these incidences over F311-bar.

At this prime the cyclic action splits into five characters. A vector of
weight a has entry zeta^(ai) x_(j-i), where zeta has order five. Its top
permanent equals F(x), the permanent of the circulant matrix x_(j-i), since
the row factors multiply to 1. The projective quintic F=0 is smooth. It
therefore contains no projective plane: on a plane it would belong to the
ideal of its two linear normal coordinates, and the two normal derivatives,
quartics on the plane, have a common projective zero. Hence each weight
space has dimension at most two.

For weight zero, all the coefficients of per(J+t*circ(x))-120 must vanish.
In the chart x_0=1, the coordinate algebra has dimension 20. The code checks
20 distinct points there, related by x_i -> x_(ki+l) and scaling, so these
are all points even over the algebraic closure. All nonzero fixed vectors
can be rotated into the chart. Thus the fixed weight space has dimension <=1.

Consider the fixed direction Z=circ(z) corresponding to one such point.
Along J+tZ, the Hessian pairs weights a and -a to zero on L x L. Write
this pairing as a 5x5 matrix M_0+t M_1+t^2 M_2+t^3 M_3 on their offset
vectors. If both spaces have dimension two, let U be a two-row coefficient
matrix for the weight-a plane. Its two-dimensional partner annihilates the
eight rows of [U M_0; ...; U M_3], so the stacked matrix has rank <=3.
For the representative z and both pairs a=1,2, every RREF chart for U has
incompatible fourth minors. Singular checks a polynomial combination of those
minors equal to 1. Offset translations correspond to shifting columns; index
multiplication relabels rows and columns simultaneously and permutes character
labels. Since both opposite pairs were checked, the same applies to all 20
directions. With a nonzero fixed direction each opposite pair therefore sums
to at most three, for a total of at most seven. With no fixed direction the
four nontrivial spaces sum to at most eight.
"""
import argparse
import itertools
import subprocess
from collections import Counter
from math import prod

P = 311
PERMS = list(itertools.permutations(range(5)))
Z = (1, 11, 186, 140, 284)
NAMES = "abcdef"
RING = "ring r=311,(a,b,c,d,e,f),dp;\n"
CHECK = ('matrix multipliers=lift(I,ideal(1));matrix check=matrix(I)*multipliers;\n'
         'if(check[1,1]==1){print("CERTIFIED");}\n')


def singular(path, script, expected):
    r = subprocess.run([path, "-q"], text=True, input=RING+script+"exit;\n",
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    if r.stdout.strip() != expected:
        raise RuntimeError(r.stdout)


def coefficients():
    polynomials = [Counter() for _ in range(6)]
    for permutation in PERMS:
        cells = [(j-i) % 5 for i, j in enumerate(permutation)]
        for k in range(6):
            polynomials[k].update(tuple(sorted(s)) for s in itertools.combinations(cells, k))
    return polynomials


def poly_string(poly):
    return "+".join("*".join([str(c)]+[NAMES[j] for j in mono]) for mono,c in poly.items())


def check_fixed_points(path, polys):
    f = poly_string(polys[5])
    singular(path, "poly F="+f+";\nideal I="+
             ",".join("diff(F,"+c+")" for c in NAMES[:5])+",a-1,f;\n"+CHECK, "CERTIFIED")
    generators = ",".join(poly_string(g) for g in polys[1:])
    singular(path, "ideal I="+generators+",a-1,f;\nprint(vdim(std(I)));\n", "20")
    orbit = set()
    for k,l in itertools.product(range(1,5), range(5)):
        z = [Z[(i*k+l)%5] for i in range(5)]
        orbit.add(tuple(x*pow(z[0], -1, P) % P for x in z))
    assert len(orbit) == 20
    for z in orbit:
        assert z[0] == 1
        assert all(sum(c*prod(z[i] for i in m) for m,c in g.items()) % P == 0
                   for g in polys[1:])


def hessians(weight):
    omega = next(x for x in range(2,P) if pow(x,5,P) == 1)
    mats = [[[0]*5 for _ in range(5)] for _ in range(4)]
    for permutation in PERMS:
        cells = [(j-i) % 5 for i,j in enumerate(permutation)]
        for i, j in itertools.permutations(range(5),2):
            remaining = [Z[cells[k]] for k in range(5) if k not in (i,j)]
            phase = pow(omega, weight*(i-j)%5, P)
            for degree in range(4):
                value = sum(prod(v) for v in itertools.combinations(remaining, degree))
                mats[degree][cells[i]][cells[j]] += phase*value
    return [[[x%P for x in row] for row in mat] for mat in mats]


def chart(pivots):
    rows = [[str(int(j==p)) for j in range(5)] for p in pivots]
    var = 0
    for row, pivot in zip(rows,pivots):
        for j in range(pivot+1,5):
            if j not in pivots:
                row[j] = NAMES[var]
                var += 1
    return rows


def check_hessians(path):
    for weight in (1,2):
        mats = hessians(weight)
        for pivots in itertools.combinations(range(5),2):
            rows = chart(pivots)
            entries = ["+".join(x+"*"+str(m[i][j]) for i,x in enumerate(row))
                       for m in mats for row in rows for j in range(5)]
            singular(path, "matrix H[8][5]="+",".join(entries)+";\n"
                     +"ideal I=minor(H,4);\n"+CHECK, "CERTIFIED")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--singular", default="Singular")
    binary = parser.parse_args().singular
    check_fixed_points(binary, coefficients())
    print("Smooth circulant quintic; 20 fixed projective directions in one orbit.")
    check_hessians(binary)
    print("Two opposite pairs, ten charts each: all twenty identities verified over F311.")
    print("Simultaneous cyclic shift: dimension <= 8, or <= 7 with a nonzero fixed direction.")
