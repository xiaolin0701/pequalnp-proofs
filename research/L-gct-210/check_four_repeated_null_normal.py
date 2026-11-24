"""Certify the complete four-active repeated-value branch in characteristic zero."""

import argparse
from itertools import combinations
import shutil

import sympy as sp
from flint import fmpz_mpoly, fmpz_mpoly_ctx

from check_four_active_null_normal import gram_program, run
from check_three_active_null_generic import remove_invertible_factors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    args = parser.parse_args()
    singular = shutil.which(args.singular)
    if not singular:
        parser.error("Singular executable missing; pass --singular /path/to/Singular")
    s = sp.Symbol("s")
    a, b = 4 * s**3, 3 * s**4
    ring = fmpz_mpoly_ctx.get(("l", "s"))
    l, value = ring.gens()
    inv = (
        l
        * value
        * (value**3 - 5)
        * (value**4 - 4 * value**3 - 5)
        * (1 + 4 * value**3 + 3 * value**4)
    )
    minors = []
    for line in run(singular, gram_program(b, a)):
        poly = remove_invertible_factors(fmpz_mpoly(line, ring), inv)
        if poly not in minors and -poly not in minors:
            minors.append(poly)
    minors.sort(key=lambda f: sum(f.degrees()))
    assert len(minors) == 10
    common = None
    degrees = []
    for j in (1, 2, 3):
        resultant = minors[0].resultant(minors[j], "l")
        if common is None:
            common = remove_invertible_factors(resultant, inv)
        else:
            common = common.gcd(resultant)
        degrees.append(common.degrees()[1])
    assert degrees == [83, 72, 0]
    print("Open-chart integer resultant gcd degrees 83, 72, 0.")

    factors = (s**3 - 5, s**3 - 5 * s**2 + 5 * s - 5, 3 * s**2 - 2 * s + 1, s + 1)
    for factor in factors:
        modulus = sp.Poly(factor, s)
        assert modulus.is_irreducible
        basis = run(singular, gram_program(b, a, modulus=modulus))
        print(f"{factor} reduced basis: {basis}")
        if factor == s + 1:
            assert "l^4" in basis
        else:
            for variable in (
                "l",
                "e3"
                if factor == factors[0]
                else "e4"
                if factor == factors[1]
                else "e5",
            ):
                assert any(
                    elt == variable
                    or (
                        elt.startswith(variable + "^")
                        and elt[len(variable) + 1 :].isdigit()
                    )
                    for elt in basis
                )
    root = sp.sqrt(-2)
    residual = sp.Matrix([-1, -1, 1 + root, 1 - root, 0])
    e = sp.ones(5, 1)
    p = e + residual - 5 * sp.eye(5)[:, 4]
    inverse = e * e.T / 4 - sp.eye(5) - (e - 4 * residual) * (e - 4 * residual).T / 20

    def omitted(order):
        return sp.Matrix(
            [
                sum(
                    sp.prod(term)
                    for term in combinations([p[i] for i in range(5) if i != j], order)
                )
                for j in range(5)
            ]
        )

    second, third = omitted(2), omitted(3)
    assert sp.simplify((second.T * inverse * second)[0]) == -sp.Rational(456, 5)
    assert sp.simplify((second.T * inverse * third)[0]) == 96
    print("Double-resonant inverse column pairings -456/5 and 96.")


if __name__ == "__main__":
    main()
