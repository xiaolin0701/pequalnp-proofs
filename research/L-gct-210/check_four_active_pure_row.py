"""Verify the pure-row obstruction for all four-active residual vectors.

Requires SymPy, python-flint, Singular 4 and msolve. The two saturation
tests use expanded integer polynomials and the rational ground field.
"""

import argparse
from itertools import combinations
from pathlib import Path
import shutil
import subprocess
import tempfile

from flint import fmpz_mpoly, fmpz_mpoly_ctx
import sympy as sp

from check_four_active_null_normal import run, spectrum_program
from check_three_active_null_generic import remove_invertible_factors


def saturated_square(singular, msolve, a, b):
    ring = fmpz_mpoly_ctx.get(("a", "b"))
    first, second = ring.gens()
    invert = second * (256 * second**3 - 27 * first**4)
    equations = [
        str(remove_invertible_factors(fmpz_mpoly(line, ring), invert)).replace(" ", "")
        for line in run(singular, spectrum_program(b, a))
    ]
    z, k = sp.symbols("z k")
    chi = sp.Poly(
        (
            5 * z**4
            + 12 * a * z**3
            + (-33 * a + 16 * b - 30) * z**2
            + (20 * a - 60 * b - 40) * z
            + 60 * a
            + 85 * b
            - 15
        )
        / 5,
        z,
    )
    first_coeff = chi.nth(3) / 2
    second_coeff = (chi.nth(2) - first_coeff**2) / 2
    defects = (
        2 * first_coeff * second_coeff - chi.nth(1),
        second_coeff**2 - chi.nth(0),
    )
    with tempfile.TemporaryDirectory() as directory:
        source, target = Path(directory) / "system.in", Path(directory) / "system.out"
        for defect in defects:
            rabinowitsch = k * b * (256 * b**3 - 27 * a**4) * defect - 1
            polynomial = sp.Poly(rabinowitsch, k, a, b).clear_denoms()[1].as_expr()
            last = str(polynomial).replace("**", "^").replace(" ", "")
            source.write_text("a,b,k\n0\n" + ",\n".join(equations + [last]) + "\n")
            subprocess.run([msolve, "-f", str(source), "-o", str(target)], check=True)
            if target.read_text().strip() != "[-1]:":
                raise ArithmeticError("Expected unit ideal for a nonzero square defect")
    basis = sp.groebner(defects, b, a, domain=sp.QQ)
    quartic = 29808 * a**4 + 369360 * a**3 + 1142965 * a**2 - 20500 * a - 3473000
    if (
        basis.polys[1].as_expr() != quartic / 29808
        or not sp.Poly(quartic, a).is_irreducible
    ):
        raise ArithmeticError(f"Unexpected square-locus parameter {basis}")
    print("Both square-defect saturations give the unit ideal over Q.")
    return basis, quartic


def modular_kernel(matrix, prime):
    rows = [[int(x) % prime for x in row] for row in matrix.tolist()]
    leading = []
    for j in range(matrix.cols):
        i = len(leading)
        pivot = next((k for k in range(i, matrix.rows) if rows[k][j]), None)
        if pivot is None:
            continue
        rows[i], rows[pivot] = rows[pivot], rows[i]
        scale = pow(rows[i][j], -1, prime)
        rows[i] = [x * scale % prime for x in rows[i]]
        for k in range(matrix.rows):
            if k != i:
                factor = rows[k][j]
                rows[k] = [(x - factor * y) % prime for x, y in zip(rows[k], rows[i])]
        leading.append(j)
    free = [j for j in range(matrix.cols) if j not in leading]
    basis = sp.zeros(matrix.cols, len(free))
    for i, j in enumerate(free):
        basis[j, i] = 1
        for k, col in enumerate(leading):
            basis[col, i] = -rows[k][j] % prime
    return basis


def check_square_points(basis, quartic, a, b):
    prime = 239
    values = {a: 232, b: 45}
    for poly in basis.polys:
        numerator, denominator = poly.as_expr().subs(values).as_numer_denom()
        assert int(denominator) % prime and int(numerator) % prime == 0
    assert int(sp.diff(quartic, a).subs(a, 232)) % prime
    v = sp.Matrix([39, 83, 144, 212, 0])
    for root in v[:4]:
        assert int(root**4 - 232 * root + 45) % prime == 0
    e = sp.ones(5, 1)
    fifth = sp.eye(5)[:, 4]
    p = e + v - 5 * fifth
    hessian = e * e.T - sp.eye(5)
    second = sp.diag(*p) - (e * p.T + p * e.T) * pow(2, -1, prime)
    space = modular_kernel((e + v).T, prime)
    restricted = modular_kernel((e + v).T.col_join(fifth.T), prime)
    assert (restricted.T * second * restricted).det() % prime == 119
    qspace = modular_kernel(e.T.col_join(v.T).col_join(fifth.T), prime)
    rows = []
    for eigenvalue, expected in ((130, (76, 19)), (213, (229, 163))):
        matrix = space.T * (second - eigenvalue * hessian) * space
        h = (space * modular_kernel(matrix, prime)).applyfunc(lambda x: x % prime)
        assert h.shape == (5, 1)
        elements = tuple(
            sum(sp.prod(c) for c in combinations(h, k)) % prime for k in (3, 4)
        )
        assert elements == expected
        rows.append(
            ((h.multiply_elementwise(h) - sum(h) * h).T * qspace).applyfunc(
                lambda x: x % prime
            )
        )
    assert rows[0].col_join(rows[1]).det() % prime == 81
    print(
        "At the split place over 239, mean determinant 119 and tangent determinant 81."
    )


def check_repeated(singular):
    s = sp.Symbol("s")
    ring = fmpz_mpoly_ctx.get(("s",))
    common = ring.constant(0)
    for line in run(singular, spectrum_program(3 * s**4, 4 * s**3, repeated=s)):
        common = common.gcd(fmpz_mpoly(line, ring))
    if common // common.content() != ring.gens()[0] ** 49:
        raise ArithmeticError("Unexpected repeated-root spectrum gcd")
    print("The primitive gcd for a repeated active coordinate is s^49.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--msolve", default="msolve")
    args = parser.parse_args()
    singular, msolve = shutil.which(args.singular), shutil.which(args.msolve)
    if not singular or not msolve:
        parser.error("Pass executable paths with --singular and --msolve")
    a, b = sp.symbols("a b")
    basis, quartic = saturated_square(singular, msolve, a, b)
    check_square_points(basis, quartic, a, b)
    check_repeated(singular)


if __name__ == "__main__":
    main()
