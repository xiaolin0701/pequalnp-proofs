"""Check the exceptional quadratic relation in the isotropic affine line of five column normals."""

import sympy as S
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import argparse, shutil, subprocess, tempfile


def check(msolve):
    a, b, c, d, k = S.symbols("a b c d k")

    def mon(i):
        return [S.Integer(j == i) for j in range(5)]

    def add(*vs):
        return [S.expand(sum(v[i] for v in vs)) for i in range(5)]

    def sc(t, v):
        return [S.expand(t * z) for z in v]

    def mul(v, w):
        return [
            S.expand(sum(v[j] * w[(i - j) % 5] for j in range(5))) for i in range(5)
        ]

    def su(v):
        return 5 * v[0]

    def dot(v, w):
        return su(mul(v, w))

    def tri(v, w, p):
        return S.expand(
            su(v) * su(w) * su(p)
            - su(v) * dot(w, p)
            - su(w) * dot(v, p)
            - su(p) * dot(v, w)
            + 2 * su(mul(mul(v, w), p))
        )

    e, g = mon(0), mon(1)
    q = [1, a, b, c, d]
    root = [d, 4, 0, 0, 0]  # d(e-4v)
    theta = mul(add(sc(5, e), sc(-1, q)), [d**4, d**3, d * d, d, 1])

    def cy(v):  # -20d²C v
        return add(sc(-5 * d * d * su(v), e), sc(20 * d * d, v), sc(dot(v, root), root))

    U = [mon(j) for j in [1, 2, 3]]
    Y = [cy(mul(theta, x)) for x in U]
    A = []
    B = []
    for i, j in combinations_with_replacement(range(3), 2):
        A.append(tri(U[i], U[j], q))
        B.append(S.expand((tri(U[i], q, Y[j]) + tri(U[j], q, Y[i])) / 2))
    basis = [
        a * a + 2 * c * d - 3 * b,
        2 * a * b + d * d - 3 * c,
        b * b + 2 * a * c - 3 * d,
    ]
    T = S.groebner(basis, a, b, c, d, order="grevlex", domain=S.QQ)

    def reduce(f):
        return T.reduce(S.expand(f))[1]

    forms = [reduce(x) for x in A]
    targets = [reduce(x) for x in B]
    obs = [
        reduce(forms[i] * targets[j] - forms[j] * targets[i])
        for i, j in combinations(range(6), 2)
    ]
    # One rational unit ideal covers every nonzero D with D^5 different from 1.
    eqs = basis + obs + [k * d * (d**5 - 1) - 1]
    with tempfile.TemporaryDirectory() as directory:
        source, target = Path(directory) / "minor.in", Path(directory) / "minor.out"

        def fmt(polynomial):
            return (
                str(S.Poly(polynomial, a, b, c, d, k).clear_denoms()[1].as_expr())
                .replace("**", "^")
                .replace(" ", "")
            )

        source.write_text(
            "a,b,c,d,k\n0\n" + ",\n".join(fmt(f) for f in eqs if f != 0) + "\n"
        )
        subprocess.run([msolve, "-f", str(source), "-o", str(target)], check=True)
        assert target.read_text().strip() == "[-1]:"
    endpoint = S.groebner(
        [f.subs(d, 1) for f in basis] + [a + b + c - 3], a, b, c, domain=S.QQ
    )
    assert list(endpoint) == [a - 1, b - 1, c - 1]
    print(
        "All fifteen proportionality minors give the rational unit ideal on the open chart."
    )
    print("The endpoint D=1 has rational reduced basis A-1, B-1, C-1.")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--msolve", default="msolve")
    exe = shutil.which(p.parse_args().msolve)
    if not exe:
        p.error("msolve executable missing")
    check(exe)


if __name__ == "__main__":
    main()
