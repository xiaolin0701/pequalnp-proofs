"""Check two 3-plane extension bounds in 4-by-5 rectangle permanent geometry.

Requires Python 3.8+, Singular and msolve. See RectangularSeedExtensions.md.
The calculation runs over F13. All selected constraints are necessary.
"""
import argparse
import itertools
import random
import re
import string
import subprocess
import tempfile
from math import prod
from pathlib import Path

P = 13
MATCHES = [
    tuple(5 * i + j for i, j in enumerate(cols))
    for cols in itertools.permutations(range(5), 4)
]


def real_seed(a, b, c):
    return [a, b, 0, 0, 0, a, -b, 0, 0, 0, -2*a, b, c, -b, -c, 0, 0, 0, 0, 0]


def cyclotomic_seed(a, b, c):
    # The primitive cube root is specialized to 3 in F13.
    return [
        x for u, v in ((1, 1), (3, 9), (9, 3), (0, 0))
        for x in (a*u, -a*u, b*v, c*v, 0)
    ]


def rref(rows):
    matrix = [[x % P for x in row] for row in rows]
    pivots = []
    for j in range(len(matrix[0])):
        k = len(pivots)
        idx = next((i for i in range(k, len(matrix)) if matrix[i][j]), None)
        if idx is None:
            continue
        matrix[k], matrix[idx] = matrix[idx], matrix[k]
        inverse = pow(matrix[k][j], -1, P)
        matrix[k] = [x*inverse % P for x in matrix[k]]
        for i in range(len(matrix)):
            if i != k:
                matrix[i] = [(x-matrix[i][j]*y) % P for x, y in zip(matrix[i], matrix[k])]
        pivots.append(j)
    return matrix[:len(pivots)], pivots


def quotient(seed, seed_coordinates):
    gradients = []
    for point in itertools.product(range(3), repeat=3):
        w = [1+x for x in seed(*point)]
        grad = [0] * 20
        for match in MATCHES:
            for i in match:
                grad[i] += prod(w[j] for j in match if j != i)
        gradients.append(grad)
    independent, pivots = rref(gradients)
    equations = independent + [[int(i == j) for i in range(20)] for j in seed_coordinates]
    matrix, pivots_with_slice = rref(equations)
    assert len(pivots_with_slice) == len(pivots) + 3
    basis = [
        [int(i == j) if i not in pivots_with_slice else
         -matrix[pivots_with_slice.index(i)][j] % P for i in range(20)]
        for j in range(20) if j not in pivots_with_slice
    ]
    return len(pivots), basis


def product_coefficient(w, direction_degree, deleted_column=None):
    """Coefficient of t^direction_degree in the matching sum at w+t*v."""
    coefficients = {}
    for match in MATCHES:
        if deleted_column is not None and any(i % 5 == deleted_column for i in match):
            continue
        for indices in itertools.combinations(match, direction_degree):
            fixed = prod(w[j] for j in match if j not in indices)
            coefficients[indices] = (coefficients.get(indices, 0) + fixed) % P
    return "+".join(str(c) + "*" + "*".join("v"+str(i) for i in indices)
                    for indices, c in sorted(coefficients.items()) if c) or "0"


def wedge_equations(seed):
    # Each row is a vector coefficient of the five unshifted deletion permanents.
    # If these values lie in one fixed line, all selected two-by-two minors vanish.
    points_and_seed_degrees = [
        ((1, 0, 0), 2), ((0, 1, 1), 2), ((1, 1, 0), 2), ((1, 0, 1), 2),
        ((1, 1, 1), 1), ((0, 1, 0), 1), ((1, 0, 0), 1), ((0, 0, 0), 0),
        ((1, 2, 4), 1),
    ]
    definitions, vectors = [], []
    for n, (point, degree) in enumerate(points_and_seed_degrees):
        vector = []
        for column in range(5):
            name = "m"+str(n)+str(column)
            value = product_coefficient(seed(*point), 4-degree, column)
            definitions.append("poly "+name+"="+value+";")
            vector.append(name)
        vectors.append(vector)
    minors = [
        vectors[i][a]+"*"+vectors[j][b]+"-"+vectors[i][b]+"*"+vectors[j][a]
        for i in range(1, len(vectors)) for j in range(i)
        for a, b in itertools.combinations(range(5), 2)
    ]
    random.Random(782).shuffle(minors)
    definitions.extend(["ideal E="+",".join(minors[:28])+";", "ideal T=reduce(E,std(I));"])
    return definitions


def expand(singular, folder, names, definitions, ideals):
    system = ["ring r=13,("+",".join(names)+"),dp;"] + definitions + ["short=0;", "int k;"]
    for ideal in ideals:
        system.append("for(k=1;k<=size("+ideal+");k++){print(string("+ideal+"[k]));}")
    system.append("quit;")
    input_path = folder/"expand.sing"
    input_path.write_text("\n".join(system))
    output = subprocess.run([singular, "-q", str(input_path)], check=True,
                            text=True, stdout=subprocess.PIPE).stdout.splitlines()
    if not output or any(not re.fullmatch(r"[a-z0-9+*^\-]+", p) for p in output):
        raise ValueError("Unexpected output from Singular: "+str(output[:3]))
    return [p for p in output if p != "0"]


def cone_dimension(msolve, folder, names, polys):
    input_path, basis_path = folder/"system.in", folder/"basis.out"
    input_path.write_text(",".join(names)+"\n13\n"+",\n".join(polys)+"\n")
    subprocess.run([msolve, "-f", str(input_path), "-o", str(basis_path), "-g", "1"],
                   stdout=subprocess.DEVNULL, check=True)
    listing = basis_path.read_text().split("[", 1)[1].strip()
    if not listing.endswith("]:"):
        raise ValueError("Incomplete leading ideal from msolve")
    leading = listing[:-2].strip().split(",")
    supports = [set(re.findall("["+names+"]", m)) for m in leading]
    # Dimension of a monomial ideal is the largest number of coordinate variables
    # whose subset contains no support of a generating monomial.
    return next(k for k in range(len(names), -1, -1) if any(
        all(not s <= set(t) for s in supports) for t in itertools.combinations(names, k)))


def verify(seed, coordinates, wedge, args):
    rank, basis = quotient(seed, coordinates)
    names = string.ascii_lowercase[:len(basis)]
    definitions = []
    for i in range(20):
        value = "+".join(str(row[i])+"*"+name for row, name in zip(basis, names) if row[i])
        definitions.append("poly v"+str(i)+"="+(value or "0")+";")
    rng = random.Random(473)
    points = [(0, 0, 0)] + [tuple(rng.randrange(P) for _ in range(3)) for _ in range(13)]
    equations = set()
    for point in points:
        shifted = [1+x for x in seed(*point)]
        for degree in (2, 3, 4):
            equations.add(product_coefficient(shifted, degree))
    definitions.append("ideal I="+",".join(sorted(equations))+";")
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        level = expand(args.singular, folder, names, definitions, ["I"])
        dim = cone_dimension(args.msolve, folder, names, level)
        print(seed.__name__, "gradient rank", rank, "quotient coordinates", len(names),
              "sampled level cone dimension", dim, flush=True)
        if wedge:
            assert (rank, len(names), dim) == (7, 10, 4)
            wedge_polys = expand(args.singular, folder, names, definitions+wedge_equations(seed), ["T"])
            combined = cone_dimension(args.msolve, folder, names, level+wedge_polys)
            print("sampled level and cofactor-line cone dimension", combined, flush=True)
            assert combined == 3
        else:
            assert (rank, len(names), dim) == (8, 9, 3)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--msolve", default="msolve")
    args = parser.parse_args()
    verify(real_seed, (0, 1, 12), False, args)
    verify(cyclotomic_seed, (0, 2, 3), True, args)
