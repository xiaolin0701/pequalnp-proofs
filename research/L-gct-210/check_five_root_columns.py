"""Certify maximum column projection rank on the full fifth-root null-cut family."""

import argparse
from itertools import combinations, product
import shutil

from flint import fmpz_mpoly, fmpz_mpoly_ctx
import sympy as sp

from check_four_active_null_normal import gram_program, run
from check_four_active_pure_row import modular_kernel


def factors(r):
    return (
        2 * r**2 - r + 2,
        16 * r**4 + 2 * r**3 + 10 * r**2 + 3 * r + 4,
        64 * r**6 - 16 * r**5 + 39 * r**4 + 6 * r**3 + 14 * r**2 + 5 * r + 3,
        256 * r**8
        - 192 * r**7
        + 128 * r**6
        - 24 * r**5
        + 25 * r**4
        + 6 * r**3
        + 8 * r**2
        + 3 * r
        + 1,
    )


def check_gram(singular):
    r = sp.Symbol("r")
    polynomials = factors(r)
    assert all(sp.Poly(f, r).is_irreducible for f in polynomials)

    # All other four coordinates have e_k=(-r)^k.
    def program(mod=None):
        return gram_program(r**4, -(r**3), modulus=mod, marked=r)

    lines = program()
    loc = lines.index("ideal I=minor(H,3);")
    lines[loc] = "ideal I=H[2,3],H[3,3];"
    ring = fmpz_mpoly_ctx.get(("l", "r"))
    l, z = ring.gens()
    common = ring.constant(0)
    for line in run(singular, lines):
        poly = fmpz_mpoly(line, ring).compose(ring.constant(1), z)
        common = common.gcd(poly)
    assert common // common.content() == z**5
    print("Nonresonant G23/G33 numerator gcd is r^5.")
    remaining = ({"l", "e2*e5"}, {"l"}, {"l", "e4"}, {"l", "e5"})
    for f, allowed, orthogonal in zip(
        polynomials, remaining, ((3, 4), (2, 4), (2, 3), (2, 3, 4))
    ):
        original = program(sp.Poly(f, r))
        loc = original.index("ideal I=minor(H,3);")
        nonzero = original.copy()
        nonzero[loc] = "ideal I=minor(H,3),l-1;"
        assert run(singular, nonzero) == ["1"]
        zero = original.copy()
        extra = [f"H[{i},{j}]" for i in orthogonal for j in orthogonal if i <= j]
        zero[loc] = "ideal I=minor(H,3),l," + ",".join(extra) + ";"
        assert set(run(singular, zero)) == allowed
        if f == polynomials[0]:
            # If e2 is also zero, F2 joins the gradients orthogonal to F0.
            zero[loc] = (
                "ideal I=minor(H,3),l,e2,H[2,2],H[2,3],H[2,4],H[3,3],H[3,4],H[4,4];"
            )
            assert set(run(singular, zero)) == {"l", "e2", "e5"}
        print(
            f"Degree {sp.degree(f, r)} resonance, zero-radius basis {sorted(allowed)}."
        )


def omitted(v, k):
    return sp.Matrix(
        [
            sum(
                sp.prod(term)
                for term in combinations([v[i] for i in range(5) if i != j], k)
            )
            for j in range(5)
        ]
    )


def check_quartic():
    p, r = 151, 120
    assert int(factors(sp.Integer(r))[1]) % p == 0
    v = sp.Matrix([134, 54, 15, 130, 120])
    assert all(int(x**5 - r**5) % p == 0 for x in v)
    h = sp.Matrix([1, 32, 118, 0, 0])
    assert sp.Poly(
        sp.prod(sp.Symbol("z") - c for c in h)
        - sp.Symbol("z") ** 2 * (sp.Symbol("z") ** 3 - 1),
        sp.Symbol("z"),
        modulus=p,
    ).is_zero
    e = sp.ones(5, 1)
    col = (1 + r) * e + (1 - 4 * r) * v - 5 * sp.eye(5)[:, 4]
    row_inverse = e * e.T * pow(4, -1, p) - sp.eye(5)
    col_inverse = row_inverse - (e - 4 * v) * (e - 4 * v).T * pow(20, -1, p)
    f0 = (e, e)
    f2 = (omitted(h, 2), omitted(col, 2))
    f3 = (omitted(h, 3), omitted(col, 3))

    def gram(f, g):
        return (
            int((f[0].T * row_inverse * g[0])[0] * (f[1].T * col_inverse * g[1])[0]) % p
        )

    def sharp(f):
        return row_inverse * f[0], col_inverse * f[1]

    assert (gram(f0, f2), gram(f0, f3), gram(f2, f3)) == (0, 125, 0)
    y = ((gram(f0, f3), *sharp(f2)), (-gram(f2, f3), *sharp(f0)))

    def inj(a, b, c):
        return (
            int(
                sum(a) * sum(b) * sum(c)
                - sum(a) * b.dot(c)
                - sum(b) * a.dot(c)
                - sum(c) * a.dot(b)
                + 2 * a.multiply_elementwise(b).dot(c)
            )
            % p
        )

    cubic = (
        sum(
            u * w * x * inj(a, b, c) * inj(i, j, k)
            for (u, a, i), (w, b, j), (x, c, k) in product(y, repeat=3)
        )
        % p
    )
    assert cubic == 147
    print(
        "Quartic endpoint, marked residual 120 modulo 151: actual-direction cubic 147."
    )


def check_quadratic():
    p, r = 31, 7
    assert int(factors(sp.Integer(r))[0]) % p == 0
    v = sp.Matrix([19, 25, 28, 14, 7])
    assert all(int(x**5 - r**5) % p == 0 for x in v)
    e = sp.ones(5, 1)
    space = modular_kernel((e + v).T, p)
    col = ((1 + r) * e + (1 - 4 * r) * v - 5 * sp.eye(5)[:, 4]).applyfunc(
        lambda x: x % p
    )

    def hessian(u):
        return sp.Matrix(
            5,
            5,
            lambda i, j: (
                0
                if i == j
                else sum(
                    sp.prod(term)
                    for term in combinations(
                        [u[k] for k in range(5) if k not in (i, j)], 2
                    )
                )
            ),
        )

    h = space.T * hessian(col) * space
    g = space.T * hessian(v) * space
    normals = omitted(col, 2).T.col_join(omitted(v, 2).T) * space
    gram = (normals * h.adjugate() * normals.T).applyfunc(lambda x: x % p)
    assert h.det() % p == 18 and gram == sp.Matrix([[0, 19], [19, 16]])
    mean = modular_kernel(normals, p)
    z = sp.Symbol("z")
    det = sp.Poly((mean.T * (g - z * h) * mean).det(), z)
    assert [int(c) % p for c in det.all_coeffs()] == [26, 17, 30]
    assert sp.discriminant(det.as_expr(), z) % p == 21
    print("Quadratic endpoint, marked residual 7 modulo 31: mean discriminant 21.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    singular = shutil.which(parser.parse_args().singular)
    if not singular:
        parser.error("Singular executable missing")
    check_gram(singular)
    check_quartic()
    check_quadratic()


if __name__ == "__main__":
    main()
