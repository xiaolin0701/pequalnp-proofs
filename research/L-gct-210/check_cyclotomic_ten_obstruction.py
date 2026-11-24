"""Verify the characteristic-13 four-row slices in CyclotomicTenObstruction.md.

Usage: python3 check_cyclotomic_ten_obstruction.py --singular /path/to/Singular
"""
import argparse
import random
import re
import string
import subprocess
import tempfile
from pathlib import Path

from verify_rectangular_seed_extensions import P, cyclotomic_seed, product_coefficient, quotient, rref


def lin_form(coefficients, variables):
    return "+".join(str(a) + "*" + v for a, v in zip(coefficients, variables) if a) or "0"


def run(executable):
    rank, basis = quotient(cyclotomic_seed, (0, 2, 3))
    assert (P, rank, len(basis)) == (13, 7, 10)
    names = string.ascii_lowercase[:len(basis)]
    program = ["ring R=13,(" + ",".join(names) + "),dp;"]
    for i in range(20):
        program.append("poly v" + str(i) + "=" + lin_form([row[i] for row in basis], names) + ";")

    rng = random.Random(473)
    points = [(0, 0, 0)] + [tuple(rng.randrange(P) for _ in range(3)) for _ in range(13)]
    equations = set()
    for p in points:
        d = cyclotomic_seed(*p)
        for k in (2, 3, 4):
            equations.add(product_coefficient([1+x for x in d], k))
        for j in range(5):
            for k in range(1, 5):
                equations.add(product_coefficient(d, k, deleted_column=j))
    program.append("ideal I=" + ",".join(sorted(equations)) + ";")

    # In the canonical quotient representative the first 15 entries form the
    # old three rows. Their simultaneous vanishing cuts out the pure new rows.
    controls, _ = rref([list(column) for column in zip(*[row[:15] for row in basis])])
    assert len(controls) == 7
    for i, row in enumerate(controls):
        label = "Sl" + str(i)
        program.append("ideal " + label + "=I,(" + lin_form(row, names) + ")-1;")
        program.append('print("SLICE "+string(dim(std(' + label + '))));')
    program.append("quit;")
    with tempfile.TemporaryDirectory() as directory:
        file = Path(directory) / "four_row_slices.sing"
        file.write_text("\n".join(program))
        proc = subprocess.run([executable, "-q", str(file)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    if not all(re.fullmatch(r"SLICE -?\d+", line) for line in proc.stdout.splitlines()):
        raise ValueError("Unexpected Singular output: " + proc.stdout)
    dims = [int(line.split()[1]) for line in proc.stdout.splitlines()]
    assert dims == [0, 0, 1, 1, 0, 1, 1]
    print("gradient rank", rank, "quotient variables", len(basis), "pure-row controls", len(controls))
    print("dimensions of the seven affine slices:", *dims)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    run(parser.parse_args().singular)
