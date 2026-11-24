"""Check a full-rank Gram obstruction in the fifth-root family modulo a good prime."""

from itertools import combinations_with_replacement, permutations, product

from flint import nmod_mat


PRIME = 151
TRIPLES = list(combinations_with_replacement(range(4), 3))
ORDERS = [sorted(set(permutations(triple))) for triple in TRIPLES]


def matrix(rows):
    return nmod_mat(rows, PRIME)


def inverse(value):
    return pow(int(value), -1, PRIME)


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def triple(x, y, z):
    return (sum(x)*sum(y)*sum(z)-sum(x)*dot(y, z)-sum(y)*dot(x, z)
            -sum(z)*dot(x, y)+2*sum(a*b*c for a, b, c in zip(x, y, z))) % PRIME


def harmonic_test(t, root, lam):
    indices = range(5)
    e = matrix([[1] for _ in indices])
    b = [pow(root, i, PRIME) for i in indices]
    assert len(set(b)) == 5 and pow(root, 5, PRIME) == 1
    v = matrix([[t*bi % PRIME] for bi in b])
    c = matrix([[(1+t*(b[i]+b[j])-4*t*t*b[i]*b[j]-5*(i==j)) % PRIME
                 for j in indices] for i in indices])
    unscaled = matrix([[(b[i]*lam[j]+b[j]*lam[i])*inverse(c[i, j]) % PRIME
                        for j in indices] for i in indices])
    mu = int((e.transpose()*unscaled.inv()*e)[0, 0])*inverse(20) % PRIME
    assert mu
    centered = e*e.transpose()*inverse(20)-unscaled*mu
    assert centered.rank() == 4
    metric = matrix([row[:4] for row in centered.tolist()[:4]])
    coordinates = metric.inv()*matrix(centered.tolist()[:4])
    assert coordinates.transpose()*metric*coordinates == centered
    column_inverse = c*inverse(5)
    radial = matrix([[mu*x*inverse(5*t) % PRIME for x in lam]])

    # For each input basis vector, list the four centered column tracks and the mean.
    tracks = []
    for a in range(4):
        z = matrix([[int(j == a)] for j in indices])
        z[4, 0] = -b[a]*inverse(b[4]) % PRIME
        assert not (v.transpose()*z)[0, 0]
        centered_columns = column_inverse*matrix(
            [[int(z[j, 0])*int(coordinates[d, j]) for d in range(4)] for j in indices])
        mean = column_inverse*z*inverse(20)-v*int((radial*z)[0, 0])
        rows = centered_columns.transpose().tolist()+mean.transpose().tolist()
        tracks.append([list(map(int, row)) for row in rows])

    coefficients, constant = [], []
    for i, j, k in TRIPLES:
        x, y, z = (tracks[q] for q in (i, j, k))
        coefficients.append([sum(triple(x[a], y[b], z[d]) for a, b, d in group) % PRIME
                             for group in ORDERS])
        known = 60*triple(x[4], y[4], z[4])
        for a, b1 in product(range(4), repeat=2):
            known -= 3*int(metric[a, b1])*(triple(x[4], y[a], z[b1])
                     +triple(x[a], y[4], z[b1])+triple(x[a], y[b1], z[4]))
        constant.append(known % PRIME)

    cubic_determinant = int(matrix(coefficients).det())
    inverse_metric = metric.inv()
    for a in range(4):
        coefficients.append([sum(int(inverse_metric[b, d]) for s, b, d in group if s == a) % PRIME
                             for group in ORDERS])
        constant.append(0)
    augmented = matrix([row+[value] for row, value in zip(coefficients, constant)])
    return mu, cubic_determinant, matrix(coefficients).rank(), augmented.rank()


def main():
    root, t = 59, 2
    scales = [111, 126, 58, 15, 67]
    determinants = [111, 49, 50, 144, 51]
    for d in range(5):
        lam = [pow(root, d*i, PRIME) for i in range(5)]
        actual = harmonic_test(t, root, lam)
        assert actual == (scales[d], determinants[d], 20, 21)
        print(f'Fourier mode {d}: scale {actual[0]}, cubic determinant {actual[1]}, ranks 20 and 21.')


if __name__ == '__main__':
    main()
