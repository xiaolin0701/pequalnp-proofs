"""Support restrictions for the constant 5 x 5 permanent problem.

Python 3.10+, python-flint 0.9, SymPy 1.14, and msolve 0.11 are used.
Run python support_bounds.py --msolve PATH, from any directory. An installed
msolve on PATH is the default. All symbolic Gröbner calculations use Q.

For support size 2d+1, the linear term gives a tangent hyperplane of
dimension 2d. The quadratic term is proportional to B, the off-row and
off-column pairing. If B is nonsingular, a totally isotropic d-plane L
equals its own orthogonal complement. Any covector killing L then yields
a vector of L by applying the inverse of B. The same holds for the polar
gradient of any homogeneous permanent coefficient on vectors of L. The
program generates vectors this way and tests all resulting pairings.

A complete row supplies a nonzero normal with coordinate sum 1: if its
projection contained the all-ones row, a translate could have a zero row.
In the regular cases the equations in this normal have all monomials of
one degree in their ideal modulo 103. Nonzero Macaulay minors lift to Q,
as the Gram determinant is invertible modulo 103. This rules out every
nonzero complex normal in those cases. The exceptional charts and the
spectral argument are explained in their respective functions.

Deleting a row and using the four-row bound gives minimum row and column
ranks d-7 (RowBound.lean). The enumeration checks all support types of
size 2d+1 compatible with this requirement. A smaller support can always
be extended to that size, so exclusion applies to smaller supports too.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
from math import prod

import flint

PRIME = 103


def patterns(size, min_degree):
    """One representative per support modulo row/column permutations and transpose."""
    actions = [[sum(1 << perm[j] for j in range(5) if mask >> j & 1)
                for mask in range(32)] for perm in permutations(range(5))]
    seen = set()
    for missing in combinations(range(25), 25-size):
        rows = [31] * 5
        for cell in missing:
            rows[cell // 5] ^= 1 << (cell % 5)
        rows = tuple(sorted(rows))
        if rows in seen:
            continue
        cols = tuple(sum((row >> j & 1) << i for i, row in enumerate(rows))
                     for j in range(5))
        for masks in (rows, cols):
            seen.update(tuple(sorted(action[m] for m in masks)) for action in actions)
        if min(m.bit_count() for m in (*rows, *cols)) >= min_degree:
            yield rows


def cells_of(rows):
    return [(i, j) for i in range(5) for j in range(5) if rows[i] >> j & 1]


def hessian(cells):
    # e_i - e_last is the basis of the coordinate-sum-zero hyperplane.
    def pair(x, y):
        return int(x[0] != y[0] and x[1] != y[1])
    last = cells[-1]
    return [[pair(x, y) - pair(x, last) - pair(last, y)
             for y in cells[:-1]] for x in cells[:-1]]


def equations(cells, normal, rational=False):
    names = list("abcdefg"[:len(normal)])
    if rational:
        ctx = flint.fmpq_mpoly_ctx.get(names)
        inv = flint.fmpq_mat(hessian(cells)).inv().tolist()
    else:
        ctx = flint.nmod_mpoly_ctx.get(names, PRIME)
        form = flint.nmod_mat(hessian(cells), PRIME)
        inv = [[int(v) for v in a] for a in form.inv().tolist()]
    zero = ctx.constant(0)

    def raise_covector(cov):
        d = [a - cov[-1] for a in cov[:-1]]
        v = [sum((b * x for b, x in zip(r, d) if b), zero) for r in inv]
        return v + [-sum(v, zero)]

    g = ctx.gens()
    covector = [sum((a for a, support in zip(g, normal) if cell in support), zero)
                for cell in cells]
    vectors = [raise_covector(covector)]
    degrees = [1]
    matchings = {}
    for k in range(3, 6):
        matchings[k] = [m for m in combinations(range(len(cells)), k)
                        if len({cells[i][0] for i in m}) == k
                        and len({cells[i][1] for i in m}) == k]

    def polar_gradient(args):
        k = len(args) + 1
        cov = [zero] * len(cells)
        rearrangements = set(permutations(args))
        for m in matchings[k]:
            for j, cell in enumerate(m):
                others = m[:j] + m[j+1:]
                for perm in rearrangements:
                    cov[cell] += prod(vectors[a][i] for a, i in zip(perm, others))
        return raise_covector(cov)

    for d in range(2, 5):
        for k in range(2, min(d, 4) + 1):
            for args in combinations_with_replacement(range(len(vectors)), k):
                if sum(degrees[i] for i in args) == d:
                    vectors.append(polar_gradient(args))
                    degrees.append(d)

    def row_and_column_sums(v):
        return [sum((v[i] for i, c in enumerate(cells) if c[axis] == a), zero)
                for axis in range(2) for a in range(5)]

    sums = [row_and_column_sums(v) for v in vectors]
    forms = defaultdict(list)
    seen = set()
    for i, v in enumerate(vectors):
        for j in range(i + 1):
            h = (sum((x*y for x, y in zip(v, vectors[j])), zero)
                 - sum((x*y for x, y in zip(sums[i], sums[j])), zero))
            if h:
                h = h / h.leading_coefficient() if rational else h * pow(int(h.leading_coefficient()), -1, PRIME)
                key = str(h)
                if key not in seen:
                    seen.add(key)
                    forms[degrees[i] + degrees[j]].append(h)
    return forms


@lru_cache(None)
def monomials(d, n):
    if n == 1:
        return [(d,)]
    return [(i,) + m for i in range(d+1) for m in monomials(d-i, n-1)]


def spans_degree(forms, d):
    basis = monomials(d, 5)
    index = {m: i for i, m in enumerate(basis)}
    rows = []
    for k, polynomials in forms.items():
        if k > d:
            continue
        for poly in polynomials:
            terms = list(poly.terms())
            for alpha in monomials(d-k, 5):
                row = [0] * len(basis)
                for beta, c in terms:
                    target = tuple(x+y for x, y in zip(alpha, beta))
                    row[index[target]] = int(c)
                rows.append(row)
    return flint.nmod_mat(rows, PRIME).rank() == len(basis)



def unit_ideal(executable, ctx, forms, bad_shift, obstruction=None):
    """Use exact rational coefficients. Adding z*h-1 tests h on the common zeros."""
    import subprocess
    from tempfile import TemporaryDirectory
    from pathlib import Path
    import re

    names = list(ctx.names())
    polynomials = [str(f).replace(" ", "") for fs in forms.values() for f in fs]
    normal = sum(a*b for a, b in zip(ctx.gens(), bad_shift)) - 1
    polynomials.append(str(normal).replace(" ", ""))
    if obstruction is not None:
        names.append("z")
        larger = flint.fmpq_mpoly_ctx.get(names)
        q = larger.from_dict({m+(1,): c for m, c in obstruction.terms()})-1
        polynomials.append(str(q).replace(" ", ""))
    with TemporaryDirectory() as tmp:
        src, out = Path(tmp)/"input", Path(tmp)/"basis"
        src.write_text(",".join(names)+"\n0\n"+",\n".join(polynomials)+"\n")
        subprocess.run([executable, "-f", str(src), "-o", str(out), "-g", "2", "-l", "2",
                        "-t", "1"], check=True)
        basis = out.read_text()
        assert "field characteristic: 0" in basis and re.search(r"\[\s*1\s*\]:\s*$", basis)


def pair_of_rows(rows, executable):
    """Make all two-row permanents vanish on a prospective bad affine fiber.

    In the first pattern rows 3,4 can be prescribed as (1,1,0,0,0) and
    (1,-1,0,0,0) by imposing seven scalar conditions. In the second,
    impose that rows 2,3 are e_2+t e_0 and e_2-t e_0 for a common t.
    Each target has zero permanent no matter what the other three rows do.
    Thus its vector of changes is missed by the seven-coordinate linear
    projection. Some covector killing that image has a nonzero pairing
    with the target. Rescale the pairing to 1 (sign chosen oppositely to
    the target); the required weights are (1,1,1,1,1,1,2).
    """
    import sympy as sp
    from check_certificates import derivatives

    cells = cells_of(rows)
    first = rows == (15, 23, 27, 28, 30)
    if first:
        normal = [[(i,j)] for i in (3,4) for j in (2,3,4)] + [[(4,1)]]
    else:
        assert rows == (15, 23, 27, 27, 28)
        normal = [[(i,j)] for i in (2,3) for j in (1,3,4)] + [[(2,0),(3,0)]]
    forms = equations(cells, normal, rational=True)
    ctx = forms[2][0].context()
    weights = [1]*6+[2]
    if not first:
        unit_ideal(executable, ctx, forms, weights)
        return
    # These eight exact inconsistency certificates give just three
    # possible normalized covectors, with two of a,b,c equal to -1/2.
    a,b,c,d,e,f,g = ctx.gens()
    for h in (2*g-1, a+d, b+e, c+f, 1+a+b+c, a*(2*a+1), b*(2*b+1), c*(2*c+1)):
        unit_ideal(executable, ctx, forms, weights, h)
    G = sp.Matrix(hessian(cells))
    V = sp.eye(18).col_join(-sp.ones(1,18))
    dual = V*G.inv()*V.T
    indices = [5*i+j for i,j in cells]
    for free in range(3):
        alpha = [-1,-1,-1,1,1,1,1]
        alpha[free] = alpha[free+3] = 0
        # Twice the normalized covector still gives a vector in L.
        cov = sp.Matrix([sum(t for t,s in zip(alpha,normal) if cell in s) for cell in cells])
        y = dual*cov
        point = [sp.Integer(1)]*25
        for k,v in zip(indices,y):
            point[k] += v
        _, h = derivatives(point)
        H = V.T*sp.Matrix(h).extract(indices,indices)*V
        x = sp.Symbol("x")
        polynomial = (G.inv()*H).charpoly(x).as_expr()
        # In a basis starting with a maximal common isotropic subspace,
        # det(H-xG) is the square of an off-diagonal block up to sign.
        expected = (x-6)**14*(x**2-12*x+31)*(16*x**2-258*x+1041)/16
        assert sp.expand(polynomial-expected) == 0
        assert any(exponent%2 for factor,exponent in sp.factor_list(polynomial)[1])


def singular_pattern():
    """Handle the unique rank-17 support with the original Hessian and one translate.

    A nine-plane contains the one-dimensional radical r of the form on
    the 18-dimensional tangent hyperplane. Both gradients at J and J+r
    annihilate L. The cut x_(4,3)=0 splits off r: W is now 16-dimensional,
    and L intersects W in a self-dual eight-plane for the first Hessian.
    The second Hessian vanishes on this eight-plane as well. Therefore
    T = H0^{-1} H1 preserves it, as do all spectral projectors of T.
    The 1/3-eigenspace E is the doubly centered upper-left 3 x 3 block.
    E is nondegenerate, dimension four. The spectral decomposition
    forces L to meet E in an isotropic plane (dimensions in E and its
    orthogonal complement are at most 2 and 6).
    """
    import sympy as sp
    from check_certificates import derivatives

    cells = cells_of((23,23,23,24,31))
    indices = [5*i+j for i,j in cells]
    G = sp.Matrix(hessian(cells))
    v, = G.nullspace()
    radical = [3*x for x in list(v)+[-sum(v)]]
    point = [sp.Integer(1)]*25
    for i,t in zip(indices,radical):
        point[i] += t
    g0,h0 = derivatives([1]*25)
    g1,h1 = derivatives(point)
    cuts = [[g[i] for i in indices] for g in (g0,g1)]
    cuts.append([int(cell == (4,3)) for cell in cells])
    assert radical[cells.index((4,3))] != 0
    A = sp.Matrix.hstack(*sp.Matrix(cuts).nullspace())
    H0,H1 = [sp.Matrix(h).extract(indices,indices) for h in (h0,h1)]
    B,C = A.T*H0*A, A.T*H1*A
    assert B.shape == (16,16) and B.det() != 0
    T = B.inv()*C
    x = sp.Symbol("x")
    char = T.charpoly(x).as_expr()
    assert sp.expand(char-(x-1)**4*(3*x-4)**4*(3*x-2)**4*(3*x-1)**4/3**12) == 0
    block = sp.Matrix([[((i==a)-(i==2))*((j==b)-(j==2)) for a in range(2) for b in range(2)]
                       for i,j in cells])
    assert sp.Matrix(cuts)*block == sp.zeros(3,4)
    assert (3*H1-H0)*block == sp.zeros(19,4)
    assert (block.T*H0*block).det() != 0
    # In the four nontrivial Fourier modes of the centered 3x3 block,
    # the quadratic and cubic coefficients are multiples of ad+bc and
    # a^3+b^3+c^3+d^3. Summation over the three row/column phases keeps
    # precisely the tuples of total weight zero in both coordinates.
    modes = [(i,j) for i in (1,2) for j in (1,2)]
    from itertools import combinations_with_replacement as multisets
    def surviving(k):
        return [q for q in multisets(range(4),k) if all(
            sum(modes[i][axis] for i in q)%3==0 for axis in (0,1))]
    assert surviving(2) == [(0,3),(1,2)]
    assert surviving(3) == [(i,i,i) for i in range(4)]
    # ad+bc is det[[a,b],[-c,d]]. A rank-one plane has a fixed left
    # or a fixed right factor (otherwise the sum of two generators has
    # rank two). Parametrize a=xu,b=xv,c=-yu,d=yv. The cubic is then
    # (x^3-y^3)u^3+(x^3+y^3)v^3. It never vanishes identically on a
    # plane with a nonzero fixed factor, in either ruling.


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--msolve", default="msolve")
    args = parser.parse_args()
    for d in (9,10,11):
        size = 2*d+1
        counted = Counter()
        for rows in patterns(size, d-7):
            cells = cells_of(rows)
            if rows == (23,23,23,24,31):
                singular_pattern()
                counted["spectral decomposition"] += 1
                continue
            if 31 not in rows:
                pair_of_rows(rows, args.msolve)
                counted["two-row projection"] += 1
                continue
            row = rows.index(31)
            normal = [[(row,j)] for j in range(5)]
            if rows == (23,27,29,30,31):
                forms = equations(cells,normal,rational=True)
                unit_ideal(args.msolve, forms[2][0].context(), forms, [1]*5)
                counted["normalized row covector"] += 1
                continue
            forms = equations(cells,normal)
            degree = next(k for k in (8,9,10) if spans_degree(forms,k))
            counted[f"Macaulay degree {degree}"] += 1
        if d==9:
            assert sum(counted.values()) == 32 and counted["two-row projection"] == 2
        print(f"Dimension {d}: excluded all {size}-cell support types; {dict(counted)}",flush=True)
    print("Minimum varying entries at dimensions 9, 10, 11: 20, 22, 24.")


if __name__ == "__main__":
    main()
