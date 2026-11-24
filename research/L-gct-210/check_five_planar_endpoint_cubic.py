"""Exclude the planar Gram endpoint 24 t^5=1 with its rational RUR and one cubic minor."""

import argparse
import ast
from itertools import combinations_with_replacement
from math import factorial, prod
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from flint import fmpz_poly, nmod_mat, nmod_poly


P = 131
DIM = 5
RUR_POINT = {"t": 76, "r": 53, "B": 127, "C": 43, "D": 50, "E": 47}


def recover_rur(singular, msolve, other_chart=False):
    from check_five_planar_endpoints import endpoint_system, saturated_system

    ring, equations = endpoint_system(singular, "scale")
    input_text = saturated_system(ring, equations, "scale", 0, 2 if other_chart else 1)
    with TemporaryDirectory() as work:
        input_path = Path(work) / "system.in"
        output_path = Path(work) / "rur.out"
        input_path.write_text(input_text)
        subprocess.run(
            [
                msolve,
                "-P",
                "2",
                "-t",
                "2",
                "-f",
                str(input_path),
                "-o",
                str(output_path),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return output_path.read_text()


def verify_rur(text):
    info = ast.literal_eval(text.strip().removesuffix(":"))[1]
    characteristic, dimension, number, names, _, (_, parametrization) = info
    assert (characteristic, dimension, number) == (0, 7, 200)
    minimal, derivative, coordinates = parametrization
    f = fmpz_poly(minimal[1])
    assert f.degree() == 200 and [(q.degree(), m) for q, m in f.factor()[1]] == [
        (200, 1)
    ]
    fp = nmod_poly(minimal[1], P)
    dp = nmod_poly(derivative[1], P)
    assert fp.degree() == 200 and fp.gcd(dp).degree() == 0

    for root, _ in fp.roots():
        x = int(root)
        point = {names[-1]: x}
        for name, ((_, coefficients), denominator) in zip(
            names[:-1], coordinates, strict=True
        ):
            numerator = int(nmod_poly(coefficients, P)(x))
            point[name] = -numerator * pow(denominator * int(dp(x)) % P, -1, P) % P
        if all(point[name] == value for name, value in RUR_POINT.items()):
            return point
    raise ValueError("The stated residue point is absent from the parametrization.")


def dot(x, y):
    return sum(a * b for a, b in zip(x, y)) % P


def distinct_triple(x, y, z):
    same_three = sum(a * b * c for a, b, c in zip(x, y, z))
    return (
        sum(x) * sum(y) * sum(z)
        - dot(x, y) * sum(z)
        - dot(y, z) * sum(x)
        - dot(z, x) * sum(y)
        + 2 * same_three
    ) % P


def determinant(point):
    indices = range(DIM)
    t, r = point["t"], point["r"]
    lam = [1] + [point[name] for name in ("B", "C", "D", "E")]
    v = [t * pow(r, i, P) % P for i in indices]
    assert 24 * pow(t, 5, P) % P == 1 and len(set(v)) == 5
    cinv = [
        [
            (1 + v[i] + v[j] - 4 * v[i] * v[j] - 5 * (i == j)) * pow(5, -1, P) % P
            for j in indices
        ]
        for i in indices
    ]
    gram = [
        [(v[i] * lam[j] + v[j] * lam[i]) * pow(cinv[i][j], -1, P) % P for j in indices]
        for i in indices
    ]
    phi = [[1] * DIM, gram[0], gram[1]]
    phi_matrix = nmod_mat(phi, P)
    basis_inverse = nmod_mat([[s[j] for s in phi] for j in range(3)], P).inv()
    core = nmod_mat([row[:3] for row in gram[:3]], P)
    metric = basis_inverse * core * basis_inverse.transpose()
    assert phi_matrix.transpose() * metric * phi_matrix == nmod_mat(gram, P)
    assert metric.rank() == 3
    domain = [
        [int(i == j) - int(i == 4) * v[j] * pow(v[4], -1, P) for i in indices]
        for j in range(4)
    ]
    row_triples = list(combinations_with_replacement(range(3), 3))
    result = []
    for sample in combinations_with_replacement(range(4), 3):
        c = [sum(domain[i][j] for i in sample) % P for j in indices]
        ell = dot(lam, c)
        xs = [[dot(row, [a * b for a, b in zip(c, s)]) for row in cinv] for s in phi]
        coefficients = []
        for triple in row_triples:
            multiplicity = 6 // prod(factorial(triple.count(i)) for i in set(triple))
            coefficients.append(
                multiplicity * distinct_triple(*(xs[i] for i in triple)) % P
            )
        mixed = ell**2 * distinct_triple(v, v, xs[0])
        for i in range(3):
            for j in range(3):
                mixed -= ell * int(metric[i, j]) * distinct_triple(v, xs[i], xs[j])
        result.append(coefficients + [mixed % P])

    minor = int(nmod_mat(result[:11], P).det())
    assert minor == 113
    return minor


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--msolve", default="msolve")
    parser.add_argument(
        "--rur", type=Path, help="Use a saved msolve -P 2 output for the same endpoint."
    )
    parser.add_argument(
        "--other-chart", action="store_true", help="Test the chart with C nonzero."
    )
    args = parser.parse_args()
    raw = (
        args.rur.read_text()
        if args.rur
        else recover_rur(args.singular, args.msolve, args.other_chart)
    )
    point = verify_rur(raw)
    minor = determinant(point)
    print(
        f"Irreducible degree 200, simple reduction modulo {P}, cubic determinant {minor}."
    )


if __name__ == "__main__":
    main()
