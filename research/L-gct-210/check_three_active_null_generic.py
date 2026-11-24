"""Certify the generic three-active residual branch for every nonresonant complex product.

Requires Singular 4 and python-flint. All eliminations are over the rationals
or integers; V remains an indeterminate throughout.
"""

import argparse
from itertools import combinations
from pathlib import Path
import shutil
import subprocess

from flint import fmpz_mpoly, fmpz_mpoly_ctx

from check_three_active_null_normal import jets_at, lower_terms, pivot_weights


def five_axis_equations(singular, emit):
    program = ["ring R=(0,vpar),(s,l,m),(lp(1),dp(2));"]
    for degree, values in ((0, [1]), (1, [1, 1]), (2, [0, 0, 0])):
        for i, value in enumerate(values):
            program.append(f"poly e{degree}_{i}={value};")
    for degree in (3, 4, 5):
        for i in range(degree + 1):
            base, factor = pivot_weights(degree, i)
            residual = lower_terms(degree, i, ("l", "m"))
            program.append(f"poly e{degree}_{i}=-vpar*{residual}/(({base})+({factor})*vpar);")
    program.append("ideal I=1;")  # Slot 1 is a sentinel; the five remainders follow.
    jets_at(program, 0, 1, 0, "y")
    program.extend(("for(int i=2;i<=6;i++){poly prim=cleardenom(I[i]);"
                    "number scale=leadcoef(I[i])/leadcoef(prim);"
                    "I[i]=numerator(scale)*prim;kill prim,scale;}",
                    "ring A=0,(l,m,vpar),dp;ideal IA=imap(R,I);short=0;",
                    "for(int j=2;j<=6;j++){string(IA[j]);}", "quit;"))
    source = "\n".join(program) + "\n"
    if emit:
        emit.write_text(source)
    result = subprocess.run([singular, "-q"], input=source, text=True,
                            capture_output=True, check=True)
    output = result.stdout.strip().splitlines()
    if len(output) != 5 or result.stderr:
        raise RuntimeError(result.stdout + result.stderr)
    ring = fmpz_mpoly_ctx.get(("l", "m", "vpar"))
    return [fmpz_mpoly(line, ring) for line in output]


def remove_invertible_factors(poly, invertible):
    """Allow division only by constants and factors known nonzero in this chart."""
    if not poly:
        raise ValueError("Unexpected zero equation")
    poly = poly // poly.content()
    while True:
        common = poly.gcd(invertible)
        if common.is_constant():
            return poly
        poly = poly // common


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    singular = shutil.which(args.singular)
    if not singular:
        parser.error("Singular executable not found; pass --singular /path/to/Singular")
    five = five_axis_equations(singular, args.emit)
    ring = fmpz_mpoly_ctx.get(("l", "v"))
    l, v = ring.gens()
    invertible = l*v*(v+1)*(v+5)*(v-20)*(4*v-5)*(3*v-10)
    rows = []
    for poly in five:
        coeffs = [{}, {}, {}]
        for (a, b, c), value in poly.to_dict().items():
            if b > 2:
                raise ValueError("Expected a quadratic in the second radial coefficient")
            coeffs[b][a, c] = value
        rows.append([ring.from_dict(d) for d in coeffs])

    necessary = []
    for i, j in combinations(range(5), 2):
        a, b, c = rows[i]
        d, e, f = rows[j]
        cross = (b*f-c*e, c*d-a*f, a*e-b*d)
        for k in range(j+1, 5):
            minor = sum((cross[t]*rows[k][t] for t in range(3)), ring.constant(0))
            necessary.append(remove_invertible_factors(minor, invertible))
        condition = cross[1]**2-cross[0]*cross[2]
        necessary.append(remove_invertible_factors(condition, invertible))
    necessary.sort(key=lambda poly: sum(poly.degrees()))

    common = None
    degrees = []
    for index in (1, 2, 10):
        resultant = necessary[0].resultant(necessary[index], "l")
        if common is None:
            common = remove_invertible_factors(resultant, invertible)
        else:
            common = common.gcd(resultant)
        degrees.append(common.degrees()[1])
    if degrees != [150, 30, 0] or not common.is_constant():
        raise RuntimeError(f"Unexpected resultant gcd degrees {degrees}")
    print("Integer resultant gcd degrees 150, 30, 0; every nonresonant product is excluded.")


if __name__ == "__main__":
    main()
