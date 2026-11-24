"""Prove the dense five-root, e3(q)=0 isotropic-line exclusion over Q."""

import argparse
from itertools import combinations
from pathlib import Path
import shutil
import subprocess
import tempfile

from flint import fmpz_mpoly_ctx


def verify(chart, msolve, directory):
    names = ("a", "b", "c", "d", "k") if chart == "nonzero_mean" else ("b", "t", "k")
    ring = fmpz_mpoly_ctx.get(names)
    zero, one = ring.constant(0), ring.constant(1)

    def basis(i):
        return [one if j == i else zero for j in range(5)]

    def add(*vectors):
        return [sum(coords, zero) for coords in zip(*vectors)]

    def scale(r, v):
        return [r * x for x in v]

    def mul(v, w):
        return [sum((v[j] * w[(i - j) % 5] for j in range(5)), zero) for i in range(5)]

    def total(v):
        return 5 * v[0]

    def dot(v, w):
        return 5 * sum((v[i] * w[-i % 5] for i in range(5)), zero)

    def triple(u, v, w):
        return (
            total(u) * total(v) * total(w)
            - total(u) * dot(v, w)
            - total(v) * dot(u, w)
            - total(w) * dot(u, v)
            + 2 * dot(mul(u, v), w)
        )

    def det(matrix):
        if len(matrix) == 1:
            return matrix[0][0]
        return sum(
            (
                (-1) ** i * val * det([row[:i] + row[i + 1 :] for row in matrix[1:]])
                for i, val in enumerate(matrix[0])
            ),
            zero,
        )

    e = basis(0)
    us = [basis(i) for i in (1, 2, 3)]
    if chart == "nonzero_mean":
        a, b, c, d, k = ring.gens()
        q = [one, a, b, c, d]
        radial = [d, 4, 0, 0, 0]
        theta = mul(add(scale(5, e), scale(-1, q)), [d**4, d**3, d**2, d, one])

        def image(x):
            return add(
                scale(-5 * d * d * total(x), e),
                scale(20 * d * d, x),
                scale(dot(x, radial), radial),
            )

        nonzero = d * (d**5 - 1)
        needed = [triple(q, q, q)]
    else:
        b, t, k = ring.gens()
        if chart == "mean_zero_first":
            q = [zero, zero, one, b, zero]
        elif chart == "mean_zero_second":
            q = [zero, one, b, -b * b, zero]
        else:
            q = [zero, zero, zero, one, zero]
        radial = [1, -4 * t, 0, 0, 0]
        theta = mul(scale(-1, q), [one, -t, t**2, -(t**3), t**4])

        def image(x):
            return add(
                scale(-5 * total(x), e), scale(20, x), scale(dot(x, radial), radial)
            )

        nonzero = t * (1 + t**5)
        needed = []
    ys = [image(mul(theta, u)) for u in us]
    first = [(triple(q, q, y), triple(q, q, u), zero) for u, y in zip(us, ys)]
    second = [
        (triple(q, y, y), 2 * triple(q, u, y), triple(q, u, u)) for u, y in zip(us, ys)
    ]
    for i, j in combinations(range(3), 2):
        needed.append(first[i][0] * first[j][1] - first[i][1] * first[j][0])
        for row in first:
            needed.append(det([row, second[i], second[j]]))
    needed.append(det(second))

    def primitive(f):
        f = f // f.content()
        while True:
            common = f.gcd(nonzero)
            if common.is_constant():
                return f
            f = f // common

    system = []
    for f in needed:
        if f:
            f = primitive(f)
            if f not in system and -f not in system:
                system.append(f)
    if chart == "nonzero_mean":
        # In the Fourier basis the powers of theta are independent precisely
        # when the five physical coordinate values of theta are distinct.
        columns = [e]
        for i in range(4):
            columns.append(mul(columns[-1], theta))
        separating = primitive(det(columns))
        nonzero *= separating
    system.append(k * nonzero - 1)
    source, target = directory / "input.ms", directory / "result.ms"
    source.write_text(
        ",".join(names)
        + "\n0\n"
        + ",\n".join(str(f).replace(" ", "") for f in system)
        + "\n"
    )
    subprocess.run([msolve, "-f", str(source), "-o", str(target)], check=True)
    if target.read_text().strip() != "[-1]:":
        raise ArithmeticError(f"Expected the unit ideal on {chart}")
    print(f"{chart}: rational unit ideal ({len(system)} generators).")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--msolve", default="msolve")
    msolve = shutil.which(parser.parse_args().msolve)
    if not msolve:
        parser.error("msolve missing; use --msolve /path/to/msolve")
    with tempfile.TemporaryDirectory() as directory:
        for chart in (
            "nonzero_mean",
            "mean_zero_first",
            "mean_zero_second",
            "mean_zero_last",
        ):
            verify(chart, msolve, Path(directory))


if __name__ == "__main__":
    main()
