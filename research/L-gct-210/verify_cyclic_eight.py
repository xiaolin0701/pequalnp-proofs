"""Exclude dimension eight under a cyclic permutation of five rows.

Run with Python 3.8+, SymPy and Singular 4 on PATH, or pass --singular PATH.
Calculations use rational coefficients. On each chart, Singular computes a
polynomial combination of its equations equal to 1 and checks the product.
No input file or certificate needs to be downloaded.

Let z be a primitive fifth root. Write a weight-a vector as T_ij=z^(ai) v_j.
A cyclically invariant complex space splits into column-vector spaces U_a.
The weight-zero space vanishes: identical rows give 120 product_j(1+t v_j).
For nonzero a, the top coefficient is 120 product_j v_j. Each U_a lies in
a coordinate hyperplane H_c. The quadratic mixed coefficient at weights a,-a
is -30 B(x,y), where B(x,y)=sum(x)sum(y)-x.y. The matrix of this pairing
on H_c x H_d is invertible (absolute determinant 3 or 1). Thus opposite
dimensions add to at most 4. At dimension 8 the two opposite pairs are
exact annihilators. For weights a,a,-2a the mixed coefficient is a nonzero
scalar times Q(x,y).w, where Q(x,y)_k sums x_i y_j for distinct i,j,k.
Indeed the sum of the three nontrivial row characters over three distinct
rows is 10, by inclusion-exclusion; the remaining two rows contribute 2!.

If dim U_a >= 3, choose a 3-plane h.x=0 in H_5 containing three directions
from U_a (or take such a plane inside U_a). The polynomial Q(x,x).w, after
dropping the factor 2, is sum_{i<j<=4}(S-w_i-w_j)x_i x_j with S=sum w.
It is divisible by h whenever w is in U_(-2a). Since the square terms vanish,
the other linear factor has support disjoint from h. The preimage of these
quadrics in w-space has dimension at most two:
* If h has one nonzero coordinate, the other three w_i must be equal to
  c, with S=2c; the remaining two coordinates sum to -c.
* If h has two nonzero coordinates, relabel them as 1,2. Both pairs (1,2)
  and (3,4) sum to S. Write the pairs as (S/2+x,S/2-x) and (S/2+y,S/2-y).
  The cross block has determinant -4xy, and must have rank at most one.
  Solutions lie in the union of the two two-dimensional planes x=0 or y=0.
* With support at least three, the other factor has at most one freedom,
  and the map w->Q has one-dimensional kernel, spanned by (1,1,1,1,-2).
That kernel lies in the preimage for every h and has no zero entry. Imposing
the common zero coordinate of U_(-2a) reduces its dimension to at most one.
If an opposite pair contains dim U_a>=3, saturation forces dim U_(2a)>=3
since dim U_(-2a)<=1. Applying the same fact at 2a gives dim U_a<=1.
Hence only the shape (2,2,2,2) could attain eight.

Choose U=U_1 and C=U_4 as its opposite. Fix a common zero column c_i for
each U_i. For U_1 we may use column 4, numbering 0..4. Relabel the other
columns and take all six RREF pivot pairs for U in H_4. For the two vectors
spanning U, let N be the three rows of Q(U,U) restricted to H_c3. These
annihilate U_3. Raising these covectors via the inverse B on H_c3 x H_c2
gives three vectors in U_2. Similarly, using C yields three vectors in U_3.
Consequently N and its counterpart each have rank at most two, and all
opposite-weight pairings and the remaining cubic tests vanish on these
known vectors. The generated equations are necessary even if one of the
three-vector spans has dimension less than two.

If each chart's polynomial ideal contains 1, no complex 2+2+2+2 solution
exists. This proves dim L <= 7 under the cyclic-row hypothesis and also
under the cyclic-column hypothesis by transposition.
"""
import argparse
import itertools
import subprocess
from collections import Counter
from functools import lru_cache

from sympy import Matrix, ZZ
from sympy.polys.rings import ring

_, *VARIABLES = ring("a,b,c,d", ZZ)


def coords(omitted):
    return [i for i in range(5) if i != omitted]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def insert_zero(vector, index):
    result = list(vector)
    result.insert(index, 0)
    return result


@lru_cache(None)
def adjugate(c, d):
    pairing = Matrix([[int(i != j) for j in coords(d)] for i in coords(c)])
    assert abs(pairing.det()) in (1, 3)
    return pairing.adjugate().tolist()


def raise_normal(vector, c, d):
    return insert_zero([dot(row, vector) for row in adjugate(c, d)], d)


def cubic_normal(x, y):
    sx, sy, xy = sum(x), sum(y), dot(x, y)
    return [(sx-a)*(sy-b)-xy+a*b for a, b in zip(x, y)]


def cubic_normals(basis, c):
    pairs = itertools.combinations_with_replacement(basis, 2)
    return [[row[i] for i in coords(c)] for row in (cubic_normal(x, y) for x, y in pairs)]


def minor(rows, omitted):
    a, b, c = [r[:omitted] + r[omitted+1:] for r in rows]
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) + a[1]*(b[2]*c[0]-b[0]*c[2])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def configurations():
    seen = set()
    for config in itertools.product(range(5), repeat=3):
        if config in seen:
            continue
        seen.update(tuple((p+(4,))[i] for i in config)
                    for p in itertools.permutations(range(4)))
        yield config


def equations(config, pivots):
    c4, c2, c3 = config
    free = [i for i in range(4) if i not in pivots]
    basis = [[int(j == pivot) for j in range(4)] for pivot in pivots]
    used = 0
    for row, pivot in zip(basis, pivots):
        for j in free:
            if j > pivot:
                row[j] = VARIABLES[used]
                used += 1
    dual = [[int(j == f) if j in free else -basis[pivots.index(j)][f]
             for j in range(4)] for f in free]
    u1 = [insert_zero(row, 4) for row in basis]
    u4 = [raise_normal(row, 4, c4) for row in dual]
    n3 = cubic_normals(u1, c3)
    n2 = cubic_normals(u4, c2)
    v2 = [raise_normal(row, c3, c2) for row in n3]
    v3 = [raise_normal(row, c2, c3) for row in n2]

    conditions = [minor(normals, i) for normals in (n2, n3) for i in range(4)]
    conditions.extend(dot(n, [v[i] for i in coords(c2)]) for n in n2 for v in v2)
    for known, opposite in ((v2, u1), (v3, u4)):
        for x, y in itertools.combinations_with_replacement(known, 2):
            q = cubic_normal(x, y)
            conditions.extend(dot(q, z) for z in opposite)
    return [g for g in conditions if g] + VARIABLES[used:]


def verify(conditions, singular):
    if any(not hasattr(g, "terms") or all(sum(m) == 0 for m, _ in g.terms())
           for g in conditions):
        return "constant"
    polys = ",\n".join(str(g).replace(" ", "").replace("**", "^") for g in conditions)
    script = ("ring r=0,(a,b,c,d),dp;\nideal I=" + polys
              + ";\nmatrix M=lift(I,ideal(1));\nmatrix T=matrix(I)*M;\n"
              + 'if(T[1,1]==1){print("CERTIFIED");}\nexit;\n')
    result = subprocess.run([singular, "-q"], input=script, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    if result.stdout.strip() != "CERTIFIED":
        raise RuntimeError(result.stdout)
    return "rational combination"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--singular", default="Singular")
    opts = parser.parse_args()
    counts = Counter()
    for config in configurations():
        for pivots in itertools.combinations(range(4), 2):
            counts[verify(equations(config, pivots), opts.singular)] += 1
    assert counts == {"constant": 37, "rational combination": 53}, counts
    print("90 charts excluded: 37 nonzero constants, 53 exact rational identities equal to 1.")
    print("Every cyclic-row-stable complex level space in the five-by-five problem has dimension <= 7.")


if __name__ == "__main__":
    main()
