"""Reproduce the characteristic-zero nonresonant four-active obstruction.

The Gram system is solved over Q. Its univariate parametrization is reduced
at a good prime to certify that the additional mixed cubic has no common root.
Requires SymPy, python-flint, Singular 4 and msolve.
"""

import argparse
import ast
from functools import cache
from math import comb, factorial
from pathlib import Path
import shutil
import subprocess
import tempfile

from flint import fmpz_mpoly, fmpz_mpoly_ctx, nmod_poly
import sympy as S

from check_four_active_null_normal import gram_program, run
from check_three_active_null_generic import remove_invertible_factors


def parametrize(singular, msolve):
    a, b = S.symbols("a b")
    ring = fmpz_mpoly_ctx.get(("l", "a", "b"))
    l, a0, b0 = ring.gens()
    inverted = l * b0 * (a0 - 20) * (b0 - 3 * a0 - 15) * (1 + a0 + b0)
    minors = []
    for line in run(singular, gram_program(b, a)):
        poly = remove_invertible_factors(fmpz_mpoly(line, ring), inverted)
        if poly not in minors and -poly not in minors:
            minors.append(poly)
    if len(minors) != 10:
        raise ArithmeticError("Expected ten distinct Gram minors")
    extended = fmpz_mpoly_ctx.get(("l", "a", "b", "k"))
    ll, aa, bb, k = extended.gens()
    equations = [str(f).replace(" ", "") for f in minors]
    equations.append(str(k * inverted.compose(ll, aa, bb) - 1).replace(" ", ""))
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "gram.in"
        result = Path(directory) / "gram.param"
        source.write_text("l,a,b,k\n0\n" + ",\n".join(equations) + "\n")
        subprocess.run(
            [
                msolve,
                "-f",
                str(source),
                "-P",
                "1",
                "-L",
                "1",
                "-t",
                "2",
                "-o",
                str(result),
            ],
            check=True,
        )
        output = result.read_text()
    return output, minors


def certify(output, minors):
    p = 10007
    # The parametrization precedes optional real-root isolation intervals.
    i = output.index("[1,\n[[")
    level = 0
    for j in range(i, len(output)):
        level += (output[j] == "[") - (output[j] == "]")
        if level == 0:
            break
    raw = ast.literal_eval(output[i : j + 1])[1]
    f = nmod_poly([int(x) % p for x in raw[0][1]], p)
    q = f * pow(int(f.leading_coefficient()), -1, p)
    den = nmod_poly([int(x) % p for x in raw[1][1]], p)
    assert q.degree() == 167 and q.gcd(q.derivative()).degree() == 0

    def inv(f):
        d, g, b = f.xgcd(q)
        assert d.degree() == 0, (d, f)
        return g * pow(int(d[0]), -1, p) % q

    def const(a):
        return nmod_poly([int(a) % p], p)

    L, A, B = [
        (-nmod_poly([int(x) % p for x in x[1]], p) * inv(den * const(y))) % q
        for x, y in raw[2]
    ]
    k = nmod_poly([0, 1], p)

    def prod(vs):
        v = const(1)
        for w in vs:
            v = (v * w) % q
        return v

    assert (prod([k, L, B, A - 20, B - 3 * A - 15, 1 + A + B]) - 1).degree() == -1
    print(
        "The rational parametrization has 167 reduced points at the good prime 10007.",
        flush=True,
    )
    for minor in minors:
        values = [L, A, B]
        power = [
            [value.pow_mod(i, q) for i in range(degree + 1)]
            for value, degree in zip(values, minor.degrees())
        ]
        checked = (
            sum(
                (
                    int(c) % p * prod([power[0][i], power[1][j], power[2][k]])
                    for (i, j, k), c in minor.to_dict().items()
                ),
                const(0),
            )
            % q
        )
        assert checked.degree() == -1

    class K:
        """An element of the finite reduced algebra F_p[z]/(q)."""

        def __init__(self, x):
            self.f = (
                x.f
                if isinstance(x, K)
                else x % q
                if isinstance(x, nmod_poly)
                else const(x)
            )

        def __add__(self, b):
            return K(self.f + K(b).f)

        __radd__ = __add__

        def __sub__(self, b):
            return K(self.f - K(b).f)

        def __rsub__(self, b):
            return K(K(b).f - self.f)

        def __mul__(self, b):
            return K(self.f * K(b).f)

        __rmul__ = __mul__

        def __truediv__(self, b):
            return K(self.f * inv(K(b).f))

        def __rtruediv__(self, b):
            return K(K(b).f * inv(self.f))

        def __pow__(self, n):
            return K(self.f.pow_mod(n, q))

        def __neg__(self):
            return K(-self.f)

        def __bool__(self):
            return bool(self.f)

    L, A, B = map(K, (L, A, B))
    aa, bb, x, y = S.symbols("aa bb x y")
    pure = (1 + x) ** 4 + aa * (1 + x) * (x + y) ** 3 + bb * (x + y) ** 4
    full = S.Poly((1 - 4 * x) * pure, x, y)
    whole = S.Poly(pure, x, y)

    def coeff(poly, r, d):
        c = S.Poly(poly.coeff_monomial(x**r * y**d), aa, bb)
        return sum((int(const) * A**i * B**j for (i, j), const in c.terms()), K(0))

    E = [K(1), K(1), K(0)]
    for k_ in (3, 4, 5):
        rhs = sum(
            (
                E[r] * (-L) ** (k_ - r) * coeff(full, r, k_ - r) / comb(5, r)
                for r in range(k_)
            ),
            K(0),
        )
        E.append(-rhs * comb(5, k_) / coeff(full, k_, 0))

    def newton(elems, N):
        """Newton row and column power sums used by the traces below."""
        n = len(elems) - 1
        tr = [K(n)]
        for k_ in range(1, N + 1):
            total = sum(
                (
                    (-1) ** (j + 1) * elems[j] * tr[k_ - j]
                    for j in range(1, min(n + 1, k_))
                ),
                K(0),
            )
            if k_ <= n:
                total += (-1) ** (k_ + 1) * k_ * elems[k_]
            tr.append(total)
        return tr

    WT = newton(E, 15)
    VT = newton([K(1), K(0), K(0), A, B], 15)

    def add(a, b):
        out = [K(0)] * max(len(a), len(b))
        for i, c in enumerate(a):
            out[i] += c
        for i, c in enumerate(b):
            out[i] += c
        return out

    def scale(k, a):
        return [k * c for c in a]

    def mul(a, b):
        out = [K(0)] * (len(a) + len(b) - 1)
        for i, c in enumerate(a):
            for j, d in enumerate(b):
                out[i + j] += c * d
        return out

    def trace(a, m):
        return sum((a[i] * m[i] for i in range(len(a))), K(0))

    def cadd(a, b):
        return (add(a[0], b[0]), a[1] + b[1])

    def cscale(k, a):
        return (scale(k, a[0]), k * a[1])

    def cprod(a, b):
        return (mul(a[0], b[0]), a[1] * b[1])

    def ctrace(a):
        return trace(a[0], VT) + a[1]

    cone = ([K(1)], K(1))
    vt = ([K(0), K(1)], K(0))
    pt = ([K(1), K(1)], K(-4))
    xx = cadd(cone, cscale(-4, vt))
    rowe = [K(1)]
    wr = [K(0), K(1)]

    @cache
    def tcol(r, d):
        t = [coeff(full, r, d)]
        if r:
            t = add(t, scale(-1, mul([K(1), K(1)], tcol(r - 1, d)[0])))
        if d:
            t = add(t, scale(-1, mul([K(0), K(1)], tcol(r, d - 1)[0])))
        return (t, coeff(whole, r, d))

    def dualrow(a):
        return add([trace(a, WT) / 4], scale(-1, a))

    def dualcol(a):
        return cadd(
            cadd(cscale(ctrace(a) / 4, cone), cscale(-1, a)),
            cscale(-ctrace(cprod(a, xx)) / 20, xx),
        )

    def jet(k_):
        return [
            (
                factorial(r) * factorial(4 - r) * (-L) ** (k_ - r),
                [(-1) ** i * E[r - i] for i in range(r + 1)],
                tcol(r, k_ - r),
            )
            for r in range(k_ + 1)
        ]

    def dual(jet):
        return [(c, dualrow(a), dualcol(b)) for c, a, b in jet]

    def pair(a, b):
        return sum(
            (
                c * d * trace(mul(f, g), WT) * ctrace(cprod(i, j))
                for c, f, i in a
                for d, g, j in b
            ),
            K(0),
        )

    F = {i: jet(i) for i in [0, 2, 3, 4]}
    D = {i: dual(f) for i, f in F.items()}
    G = {(i, j): pair(f, d) for i, f in F.items() for j, d in D.items()}
    r2 = G[0, 2]
    assert q.gcd(r2.f).degree() == 0

    def jetscale(c, J):
        return [(s * c, a, b) for s, a, b in J]

    def actual(i, j):
        ri = G[0, i]
        rj = G[0, j]
        return (
            jetscale(ri * ri, D[j])
            + jetscale(-ri * rj, D[i])
            + jetscale(-(ri * G[j, i] - rj * G[i, i]), D[0])
        )

    Z = [(K(1), wr, pt), (-L, rowe, vt)]

    def cub(a, b, c, fun, t):
        """Sum over ordered triples of distinct indices by inclusion-exclusion."""
        sa, sb, sc = t(a), t(b), t(c)
        return (
            sa * sb * sc
            - sa * t(fun(b, c))
            - sb * t(fun(a, c))
            - sc * t(fun(a, b))
            + 2 * t(fun(fun(a, b), c))
        )

    def trilinear(J, Kk, W):
        out = K(0)
        for a, f, i in J:
            for b, g, j in Kk:
                for c, h, k in W:
                    row = cub(f, g, h, mul, lambda a: trace(a, WT))
                    if row:
                        out += a * b * c * row * cub(i, j, k, cprod, ctrace)
        return out

    tangent = actual(2, 3)
    mixed = trilinear(Z, tangent, tangent)
    assert q.gcd(mixed.f).degree() == 0
    print("Both the 0,2 Gram entry and the mixed cubic are units at all 167 points.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--msolve", default="msolve")
    args = parser.parse_args()
    singular, msolve = shutil.which(args.singular), shutil.which(args.msolve)
    if not singular or not msolve:
        parser.error("Pass executable paths with --singular and --msolve")
    certify(*parametrize(singular, msolve))


if __name__ == "__main__":
    main()
