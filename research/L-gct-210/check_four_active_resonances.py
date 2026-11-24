"""Exact verification of all three resonant lines in the four-active null cut."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from flint import fmpz_mpoly, fmpz_mpoly_ctx
import sympy as sp

from check_four_active_null_normal import gram_program, run
from check_three_active_null_generic import remove_invertible_factors


def gram_constraints(a, b, indices):
    lines = gram_program(b, a)
    eligible = [j for j in (2, 3, 4) if j not in indices]
    extra = [f"H[{i},{j}]" for i in eligible for j in eligible if i <= j]
    loc = lines.index("ideal I=minor(H,3);")
    if extra:
        lines[loc] = "ideal I=minor(H,3)," + ",".join(extra) + ";"
    return lines


def check_lines(singular, msolve):
    s = sp.Symbol("s")
    profiles = ((3, sp.Integer(20), s), (4, s, 3 * s + 15), (5, s, -1 - s))
    with tempfile.TemporaryDirectory() as directory:
        source, target = Path(directory) / "input.ms", Path(directory) / "out.ms"
        for number, a, b in profiles:
            ring = fmpz_mpoly_ctx.get((f"e{number}", "l", "s"))
            e, l, value = ring.gens()
            units = sp.expand(
                b * sp.prod(x for x in (a - 20, b - 3 * a - 15, 1 + a + b) if x != 0)
            )
            base = fmpz_mpoly(str(units).replace("**", "^"), ring)
            extended = fmpz_mpoly_ctx.get((f"e{number}", "l", "s", "k"))
            ee, ll, ss, k = extended.gens()
            for zero_radius in (False, True):
                # F_i is orthogonal to F_0 when l=0 and e_i(w)=0.
                program = (
                    gram_constraints(a, b, {number})
                    if zero_radius
                    else gram_program(b, a)
                )
                inverted = base * (e if zero_radius else l)
                equations = []
                for line in run(singular, program):
                    poly = fmpz_mpoly(line, ring)
                    if zero_radius:
                        poly = poly.compose(e, ring.constant(0), value)
                    if poly:
                        poly = remove_invertible_factors(poly, inverted)
                        if poly not in equations and -poly not in equations:
                            equations.append(poly)
                if zero_radius:
                    equations.append(l)
                if zero_radius and number == 3:
                    assert value - 1005 in equations or 1005 - value in equations
                    print("Third-order resonance, zero radius: B must be 1005.")
                    continue
                if not any(f.is_constant() for f in equations):
                    formatted = [str(f).replace(" ", "") for f in equations]
                    formatted.append(
                        str(k * inverted.compose(ee, ll, ss) - 1).replace(" ", "")
                    )
                    source.write_text(
                        f"e{number},l,s,k\n0\n" + ",\n".join(formatted) + "\n"
                    )
                    subprocess.run(
                        [msolve, "-f", str(source), "-o", str(target)], check=True
                    )
                    assert target.read_text().strip() == "[-1]:"
                print(f"Resonance {number}, zero radius {zero_radius}: unit ideal.")


def check_crossings(singular):
    for a, b, i, j in ((20, 75, 3, 4), (20, -21, 3, 5), (-4, 3, 4, 5)):
        a, b = sp.Integer(a), sp.Integer(b)
        nonzero = gram_program(b, a)
        if i == 3:
            # The third-order compatibility is A*l^2*(3/5-l)=0.
            loc = nonzero.index("ideal I=minor(H,3);")
            nonzero[loc] = "ideal I=minor(H,3),5*l-3;"
            assert run(singular, nonzero) == ["1"]
        else:
            assert "l^4" in run(singular, nonzero)
        zero = gram_constraints(a, b, {i, j})
        loc = next(
            k for k, line in enumerate(zero) if line.startswith("ideal I=minor(H,3)")
        )
        zero[loc] = zero[loc][:-1] + ",l;"
        basis = set(run(singular, zero))
        expected = {
            (20, 75): {"l", "e4^3", "e3+2*e4"},
            (20, -21): {"l", "e5", "e3"},
            (-4, 3): {"l", "e5", "e4"},
        }[(a, b)]
        assert basis == expected
        print(f"({a},{b}) zero-radius reduced basis: {sorted(basis)}")


def check_last_profile():
    t, e = sp.symbols("t e")

    def traces(elementary, count):
        n = len(elementary) - 1
        trace = [sp.Integer(n)]
        for k in range(1, count + 1):
            value = sum(
                (-1) ** (j + 1) * elementary[j] * trace[k - j]
                for j in range(1, min(n + 1, k))
            )
            if k <= n:
                value += (-1) ** (k + 1) * k * elementary[k]
            trace.append(sp.expand(value))
        return trace

    row_sums = traces([1, 1, 0, e, 0, 0], 12)
    col_sums = traces([1, 0, 0, 20, 1005], 12)

    def trace(f, sums):
        return sp.expand(sum(c * sums[i] for (i,), c in sp.Poly(f, t).terms()))

    def rt(q):
        return trace(q, row_sums)

    def ct(q):
        return trace(q[0], col_sums) + q[1]

    def cmul(x, y):
        return x[0] * y[0], x[1] * y[1]

    def cscale(k, x):
        return k * x[0], k * x[1]

    def cadd(x, y):
        return x[0] + y[0], x[1] + y[1]

    ones, coord, rad = (1, 1), (1 + t, -4), (1 - 4 * t, 1)

    def dual_col(q):
        return cadd(
            cadd(cscale(ct(q) / 4, ones), cscale(-1, q)),
            cscale(-ct(cmul(q, rad)) / 20, rad),
        )

    def dual_row(f):
        return rt(f) / 4 - f

    symmetric = [1, 0, -10, 0, 930, -4104]

    def omit(k):
        return tuple(
            sp.expand(sum((-c) ** i * symmetric[k - i] for i in range(k + 1)))
            for c in coord
        )

    f0 = (1, ones)
    f2 = (t * t - t, omit(2))
    f3 = (e + t * t - t**3, omit(3))

    def gram(f, g):
        return sp.factor(rt(f[0] * dual_row(g[0])) * ct(cmul(f[1], dual_col(g[1]))))

    assert gram(f0, f2) == 0 and gram(f0, f3) == 1920 * e and gram(f2, f3) == 0

    def inj(f, g, h, mul, tr):
        a, b, c = map(tr, (f, g, h))
        return sp.expand(
            a * b * c
            - a * tr(mul(g, h))
            - b * tr(mul(f, h))
            - c * tr(mul(f, g))
            + 2 * tr(mul(f, mul(g, h)))
        )

    row = dual_row(f2[0])
    col = dual_col(f2[1])
    mixed = sp.factor(
        inj(t, row, row, lambda a, b: a * b, rt) * inj(coord, col, col, cmul, ct)
    )
    assert mixed == -1041120 * e
    print("A=20, B=1005: the mixed cubic equals -1041120*e3.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--msolve", default="msolve")
    args = parser.parse_args()
    singular, msolve = shutil.which(args.singular), shutil.which(args.msolve)
    if not singular or not msolve:
        parser.error("Pass tool paths using --singular and --msolve")
    check_lines(singular, msolve)
    check_crossings(singular)
    check_last_profile()


if __name__ == "__main__":
    main()
