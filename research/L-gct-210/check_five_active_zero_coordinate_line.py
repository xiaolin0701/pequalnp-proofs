"""Check all cubic dependence charts when one coordinate of a is zero."""

import argparse
from itertools import combinations_with_replacement, product
import shutil
import subprocess

from sympy.polys.rings import ring
from sympy import QQ


def check(singular):
    R, a, b, f = ring("a,b,f", QQ)
    P = R

    def mon(i):
        return [P(int(j == i)) for j in range(5)]

    def add(*vs):
        return [sum(v[i] for v in vs) for i in range(5)]

    def sc(t, v):
        return [t * z for z in v]

    def mul(v, w):
        return [sum(v[j] * w[(i - j) % 5] for j in range(5)) for i in range(5)]

    def su(v):
        return 5 * v[0]

    def dot(v, w):
        return su(mul(v, w))

    def tri(v, w, q):
        return (
            su(v) * su(w) * su(q)
            - su(v) * dot(w, q)
            - su(w) * dot(v, q)
            - su(q) * dot(v, w)
            + 2 * su(mul(mul(v, w), q))
        )

    for ind in range(3):
        q0, A, B = [(1, a, b), (0, 1, b), (0, 0, 1)][ind]
        q = [P(q0), A, B, 3 * q0 - A - B, P(q0)]
        theta = [f, f - A, f - A - B, f - 3 * q0, f - 4 * q0]
        e = mon(0)
        root = add(e, sc(4, mon(1)))

        def cy(v):
            return add(sc(-5 * su(v), e), sc(20, v), sc(dot(v, root), root))

        X = [mon(k) for k in [1, 2, 3]] + [sc(0, e)]
        Y = [cy(mul(theta, x)) for x in X[:3]] + [q]
        rows = []
        for i, j, k in combinations_with_replacement(range(4), 3):
            v, u, w = (X[i], Y[i]), (X[j], Y[j]), (X[k], Y[k])
            row = [P(0)] * 4
            for ii, jj, kk in product(range(2), repeat=3):
                row[ii + jj + kk] += tri(v[ii], u[jj], w[kk])
            rows.append(row)
        known = [tri(q, q, q)]
        if ind:
            known.append(a)
        if ind == 2:
            known.append(b)
        fmt = lambda x: str(x).replace("**", "^").replace(" ", "")
        lines = ["ring R=0,(a,b,f,w1,w2,w3),dp;", "option(redSB);"]
        for pivot in range(4):
            equations = [fmt(item) for item in known if item]
            for row in rows:
                parts = ["(" + fmt(row[pivot]) + ")"] if row[pivot] else []
                parts.extend(
                    "(" + fmt(row[j]) + f")*w{j}" for j in range(pivot + 1, 4) if row[j]
                )
                if parts:
                    equations.append("+".join(parts))
            equations.extend(f"w{j}" for j in range(1, pivot + 1))
            lines += [
                f"ideal I{pivot}=" + ",".join(equations) + ";",
                f"ideal G{pivot}=std(I{pivot});",
                f'if(size(G{pivot})==1 && G{pivot}[1]==1){{"unit";}}',
            ]
        result = subprocess.run(
            [singular, "-q"],
            input="\n".join(lines + ["quit;"]),
            text=True,
            capture_output=True,
            check=True,
        )
        if result.stderr or result.stdout.strip().splitlines() != ["unit"] * 4:
            raise ArithmeticError(result.stdout[:1000] + result.stderr[:1000])
        print(
            f"Projective column chart {ind + 1}: all four dependence ideals have rational basis 1."
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    singular = shutil.which(parser.parse_args().singular)
    if not singular:
        parser.error("Singular executable missing")
    check(singular)


if __name__ == "__main__":
    main()
