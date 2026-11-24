"""Classify complex lines in e2=e3=0 in the five-coordinate space."""

import argparse
import ast
from itertools import combinations, permutations
from pathlib import Path
import shutil
import subprocess
import tempfile

import sympy as sp


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--msolve", default="msolve")
    executable = shutil.which(ap.parse_args().msolve)
    if executable is None:
        ap.error("Use --msolve /path/to/msolve")
    a, b, c, d, f, g, s, t = sp.symbols("a b c d f g s t")
    coords = (s, t, a * s + b * t, c * s + d * t, f * s + g * t)
    equations = []
    for order in (2, 3):
        form = sum(sp.prod(terms) for terms in combinations(coords, order))
        equations.extend(
            sp.Poly(form, s, t).coeff_monomial(s ** (order - i) * t**i)
            for i in range(order + 1)
        )
    with tempfile.TemporaryDirectory() as directory:
        source, target = Path(directory) / "chart.ms", Path(directory) / "result.ms"
        source.write_text(
            "a,b,c,d,f,g\n0\n"
            + ",\n".join(str(p).replace(" ", "").replace("**", "^") for p in equations)
            + "\n"
        )
        subprocess.run(
            [executable, "-f", str(source), "-P", "1", "-o", str(target)], check=True
        )
        # The finite rational parametrization precedes the real isolating intervals.
        output = target.read_text()
        start = output.index("[1,\n[[")
        level = 0
        for end in range(start, len(output)):
            level += (output[end] == "[") - (output[end] == "]")
            if level == 0:
                break
        param = ast.literal_eval(output[start : end + 1])
        degree, coefficients = param[1][0]
        z = sp.Symbol("z")
        polynomial = sp.Poly(sum(c * z**i for i, c in enumerate(coefficients)), z)
        if not (polynomial.degree() == degree == 12 and polynomial.is_sqf):
            raise ArithmeticError(
                "Expected a reduced univariate parametrization of degree 12"
            )
    solutions = set()
    roots = (-1, sp.I, -sp.I)
    for vals in permutations(roots):
        solutions.add((0, vals[0], 0, vals[1], 0, vals[2]))
        solutions.add((vals[0], 0, vals[1], 0, vals[2], 0))
    assert len(solutions) == 12
    for point in solutions:
        substitutions = dict(zip((a, b, c, d, f, g), point))
        assert all(p.subs(substitutions) == 0 for p in equations)
    print(
        "One rational chart has 12 geometric points, all identified by explicit lines."
    )


if __name__ == "__main__":
    main()
