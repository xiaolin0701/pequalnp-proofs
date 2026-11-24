"""Exact checks for the fourth-root family in FourActiveNullCut.md.

Run with Python, SymPy, python-flint and Singular 4. Characteristic zero
is used throughout. In the open chart, the product of the four active
coordinates remains a free variable b.
"""

import argparse
from functools import cache
from itertools import combinations
from math import comb, factorial
import re
import shutil
import subprocess

import sympy as sp
from flint import fmpz_mpoly, fmpz_mpoly_ctx

from check_three_active_null_generic import remove_invertible_factors


def singular_form(expression):
    plain = str(sp.expand(expression)).replace("**", "^").replace(" ", "")
    return re.sub(r"\^(\d+)", r"^(\1)", plain)


def run(singular, program):
    result = subprocess.run(
        [singular, "-q"],
        input="\n".join(program + ["quit;"]),
        capture_output=True,
        text=True,
        check=True,
    )
    if result.stderr or any(
        "?" in line or "//" in line for line in result.stdout.splitlines()
    ):
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout.strip().splitlines()


def gram_program(b, a=0, modulus=None, marked=None):
    """Use a,b as the third/fourth elementary coefficients of the other four values.

    A marked nonzero fifth residual comes from a centered column normal.
    The default zero residual uses a normalized column normal instead.
    """
    marked_value = sp.Integer(0) if marked is None else marked
    offset, scale = 1 + marked_value, 1 - 4 * marked_value
    others = [1, -marked_value, marked_value**2, a, b]
    symbols = (
        sp.sympify(a).free_symbols
        | sp.sympify(b).free_symbols
        | sp.sympify(marked_value).free_symbols
    )
    parameter = next(iter(symbols)) if len(symbols) == 1 else None
    generic = bool(symbols) and modulus is None
    parameters = ",".join(sorted(map(str, symbols)))
    if modulus is not None and parameter is None:
        raise ValueError("An algebraic specialization needs one field parameter")

    def reduce_coefficient(value):
        if modulus is not None:
            return sp.rem(value, modulus.as_expr(), parameter)
        return value

    starting = (
        "poly e0=1;poly e1=1;poly e2=0;" if marked is None else "poly e0=1;poly e1=0;"
    )
    lines = [starting, "ideal compat=0;"]
    free = []
    x, y, t = sp.symbols("x y t")
    base, term = 1 + offset * x, scale * x + y
    active = sp.Poly(sum(others[k] * base ** (4 - k) * term**k for k in range(5)), x, y)
    full = sp.Poly(
        (1 + (offset + scale * marked_value - 5) * x + marked_value * y)
        * active.as_expr(),
        x,
        y,
    )

    def coeff(poly, i, j):
        return reduce_coefficient(poly.coeff_monomial(x**i * y**j))

    for k in range(3 if marked is None else 2, 6):
        pivot = coeff(full, k, 0) / comb(5, k)
        terms = [
            f"({singular_form(coeff(full, r, k - r) / comb(5, r))})*e{r}*(-l)^{k - r}"
            for r in range(k)
        ]
        residual = "+".join(terms)
        if pivot:
            lines.append(f"poly e{k}=-({residual})/({singular_form(pivot)});")
        else:
            free.append(f"e{k}")
            lines.append(f"compat=compat,({residual});")
    if generic:
        ring = f"ring R=(0,{parameters}),(" + ",".join(free + ["l"]) + "),dp;"
    elif modulus is not None and modulus.degree() > 1:
        ring = (
            f"ring R=(0,{parameter}),(" + ",".join(free + ["l"]) + "),lp;"
            f"minpoly={singular_form(modulus.as_expr())};"
        )
    else:
        ring = "ring R=0,(" + ",".join(free + ["l"]) + "),lp;"
    lines.insert(0, ring)

    lines.append("poly n0=5;")
    for k in range(1, 9):
        terms = [f"({(-1) ** (i + 1)})*e{i}*n{k - i}" for i in range(1, min(k, 6))]
        if k <= 5:
            terms.append(f"({(-1) ** (k + 1) * k})*e{k}")
        lines.append(f"poly n{k}=" + "+".join(terms) + ";")

    def row_sum(r):
        return "+".join(f"({(-1) ** i})*e{r - i}*n{i}" for i in range(r + 1))

    for r in range(5):
        for d in range(r, 5):
            dot = "+".join(
                f"({(-1) ** (i + j)})*e{r - i}*e{d - j}*n{i + j}"
                for i in range(r + 1)
                for j in range(d + 1)
            )
            lines.append(f"poly rr{r}_{d}=({row_sum(r)})*({row_sum(d)})/4-({dot});")

    powers = [sp.Integer(4)]
    for degree in range(1, 9):
        value = sum(
            (-1) ** (j + 1) * others[j] * powers[degree - j]
            for j in range(1, min(degree, 5))
        )
        if degree <= 4:
            value += (-1) ** (degree + 1) * degree * others[degree]
        powers.append(reduce_coefficient(value))

    def trace(poly):
        return sum(c * powers[i] for (i,), c in sp.Poly(poly, t).terms())

    @cache
    def column(r, s):
        active_part = coeff(full, r, s)
        if r:
            active_part -= (offset + scale * t) * column(r - 1, s)[0]
        if s:
            active_part -= t * column(r, s - 1)[0]
        return sp.expand(active_part), coeff(active, r, s)

    @cache
    def column_pair(r, s, d, z):
        f, fifth_f = column(r, s)
        g, fifth_g = column(d, z)
        sf, sg = trace(f) + fifth_f, trace(g) + fifth_g
        dot = trace(f * g) + fifth_f * fifth_g
        return sp.expand(
            reduce_coefficient(
                sf * sg / 4
                - dot
                - (sf - 4 * (trace(t * f) + marked_value * fifth_f))
                * (sg - 4 * (trace(t * g) + marked_value * fifth_g))
                / 20
            )
        )

    degrees = (0, 2, 3, 4)
    lines.append("matrix H[4][4];")
    for i, k in enumerate(degrees, 1):
        for j in range(i, 5):
            q = degrees[j - 1]
            terms = []
            for r in range(k + 1):
                for d in range(q + 1):
                    value = column_pair(r, k - r, d, q - d)
                    if value:
                        value *= (
                            factorial(r)
                            * factorial(4 - r)
                            * factorial(d)
                            * factorial(4 - d)
                        )
                        first_index, second_index = sorted((r, d))
                        terms.append(
                            f"({singular_form(value)})*(-l)^{k - r + q - d}*rr{first_index}_{second_index}"
                        )
            lines.extend(
                [
                    f"H[{i},{j}]=" + ("+".join(terms) or "0") + ";",
                    f"H[{j},{i}]=H[{i},{j}];",
                ]
            )
    lines.append("ideal I=minor(H,3);")
    if generic:
        if free:
            lines.append("I=simplify(I+compat,2);")
        names = ",".join(free + ["l", parameters])
        lines.extend(
            [
                "for(int i=1;i<=size(I);i++){if(I[i]!=0){poly p=cleardenom(I[i]);"
                "number sc=leadcoef(I[i])/leadcoef(p);I[i]=numerator(sc)*p;kill p,sc;}}",
                f"ring A=0,({names}),dp;ideal IA=imap(R,I);short=0;",
                "for(int j=1;j<=size(IA);j++){if(IA[j]!=0){string(IA[j]);}}",
            ]
        )
    else:
        lines.extend(
            [
                "option(redSB);ideal equations=I,compat;ideal gb=std(equations);short=0;",
                "for(int j=1;j<=size(gb);j++){string(gb[j]);}",
            ]
        )
    return lines


def check_gram(singular, b):
    ring = fmpz_mpoly_ctx.get(("l", "b"))
    l, product = ring.gens()
    invertible = l * product * (product - 15) * (product + 1)
    minors = []
    for line in run(singular, gram_program(b)):
        poly = remove_invertible_factors(fmpz_mpoly(line, ring), invertible)
        if poly not in minors and -poly not in minors:
            minors.append(poly)
    minors.sort(key=lambda f: sum(f.degrees()))
    assert len(minors) == 10
    common = None
    for i, j in combinations(range(len(minors)), 2):
        result = minors[i].resultant(minors[j], "l")
        if not result:
            continue
        if common is None:
            common = remove_invertible_factors(result, invertible)
        else:
            common = common.gcd(result)
        if common.is_constant():
            break
    if common is None or not common.is_constant():
        raise ArithmeticError(f"Nonconstant generic gcd: {common}")
    print("Ten minors give integer resultant gcd 1.", flush=True)
    for endpoint, expected in (
        (15, {"e4^3", "e4^2*l^2", "l^3"}),
        (-1, {"e5^3", "e5^2*l^2", "e5*l^4", "l^5"}),
    ):
        basis = set(run(singular, gram_program(sp.Integer(endpoint))))
        if basis != expected:
            raise ArithmeticError(f"Unexpected basis at b={endpoint}: {basis}")
        print(f"b={endpoint} reduced rational basis: {sorted(basis)}", flush=True)


def spectrum_program(b, a=0, repeated=None):
    t, z = sp.symbols("t z")
    powers = [4, 0, 0, 3 * a]
    for i in range(4, 9):
        powers.append(sp.expand(a * powers[i - 3] - b * powers[i - 4]))
    if repeated is None:
        size = 4
        root_polynomial = t**4 - a * t + b
        obstruction_factor = z
    else:
        size = 3
        root_polynomial = (t - repeated) * (t * t + 2 * repeated * t + 3 * repeated**2)
        obstruction_factor = z * (z + 1 + repeated)
    parameter_names = ",".join(sorted(str(v) for v in sp.sympify(b + a).free_symbols))
    fifth = sp.Matrix([-powers[i] - powers[i + 1] for i in range(size)])
    sums = sp.Matrix(powers[:size]) + fifth
    dot = sp.Matrix(size, size, lambda i, j: powers[i + j])
    weighted = sp.Matrix(size, size, lambda i, j: powers[i + j + 1])
    hessian = sums * sums.T - dot - fifth * fifth.T
    second = (
        dot + weighted - 4 * fifth * fifth.T + 5 * (sums * fifth.T + fifth * sums.T) / 2
    )
    pencil = second - z * hessian
    char = pencil.det(method="domain-ge")
    lines = [
        f"ring R=(0,{parameter_names}),(t,z),(lp(1),dp(1));",
        f"poly chi={singular_form(char)};",
        f"ideal Q=std(ideal({singular_form(root_polynomial)},chi));",
        "ideal I=1;",
    ]
    for j in range(size):
        column = [
            (-1) ** (i + j) * pencil.minor_submatrix(j, i).det(method="domain-ge")
            for i in range(size)
        ]
        vec = sum(c * t**i for i, c in enumerate(column))
        last = sum(a * c for a, c in zip(fifth, column))
        lines.extend(
            [f"poly h{j}={singular_form(vec)};", f"poly hj{j}={singular_form(last)};"]
        )
        elementary = ["1"]
        for k in range(1, 5):
            power, tr = f"pow{j}_{k}", f"tr{j}_{k}"
            lines.extend(
                [f"poly {power}=reduce(h{j}^{k},Q);", f"poly {tr}=reduce(hj{j}^{k},Q);"]
            )
            for i in range(size):
                if powers[i]:
                    lines.append(
                        f"{tr}={tr}+({singular_form(powers[i])})*subst({power},t,0)/{factorial(i)};"
                    )
                lines.append(f"{power}=diff({power},t);")
            val = "+".join(
                f"({(-1) ** (i + 1)})*{elementary[k - i]}*tr{j}_{i}"
                for i in range(1, k + 1)
            )
            elementary.append(f"e{j}_{k}")
            lines.append(f"poly {elementary[k]}=reduce(({val})/{k},Q);")
        factor = singular_form(obstruction_factor)
        lines.extend(
            [
                f"poly obs{j}=reduce(({factor})*diff(chi,z)^2*e{j}_3*e{j}_4,Q);",
                f"int k{j};for(k{j}=0;k{j}<{size};k{j}++){{I=I,subst(obs{j},z,0);"
                f"obs{j}=diff(obs{j},z);}}",
            ]
        )
    lines.extend(
        [
            "for(int i=2;i<=size(I);i++){if(I[i]!=0){I[i]=numerator(leadcoef(I[i]));}}",
            f"ring Z=0,({parameter_names}),dp;ideal J=imap(R,I);short=0;",
            "for(int j=2;j<=size(J);j++){if(J[j]!=0){string(J[j]);}}",
        ]
    )
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    args = parser.parse_args()
    singular = shutil.which(args.singular)
    if not singular:
        parser.error("Singular executable missing; pass --singular /path/to/Singular")
    b = sp.Symbol("b")
    check_gram(singular, b)
    ring = fmpz_mpoly_ctx.get(("b",))
    common = ring.constant(0)
    for line in run(singular, spectrum_program(b)):
        common = common.gcd(fmpz_mpoly(line, ring))
    if common // common.content() != ring.gens()[0] ** 26:
        raise ArithmeticError(f"Unexpected spectrum gcd {common}")
    print("Primitive gcd of the spectral remainders is b^26.")


if __name__ == "__main__":
    main()
