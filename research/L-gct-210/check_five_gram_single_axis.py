"""Exclude an isolated nonzero diagonal entry away from a single active Gram parameter."""

from functools import reduce
from itertools import combinations_with_replacement, permutations, product

from flint import nmod_mat, nmod_poly


P = 31


def matrix(rows):
    return nmod_mat(rows, P)


def column(values):
    return matrix([[x] for x in values])


def main():
    root, scale = 2, 7
    v = [scale*pow(root, j, P) % P for j in range(5)]
    assert pow(root, 5, P) == 1 and len(set(v)) == 5
    assert (2*v[0]**2-v[0]+2) % P == 0
    c = matrix([[(1+v[i]+v[j]-4*v[i]*v[j]-5*(i==j))*pow(5, -1, P) % P
                 for j in range(5)] for i in range(5)])
    assert all(c[i, j] or i == j == 0 for i in range(5) for j in range(5))
    others = (2, 3, 4)
    theta = [v[i]*pow(int(c[1, i]), -1, P) % P if i in others else 0 for i in range(5)]
    assert len({theta[i] for i in others}) == 3
    tracks = []
    for j in others[:-1]:
        z = [0]*5
        z[j] = 1
        z[4] = -v[j]*pow(v[4], -1, P) % P
        assert sum(a*b for a, b in zip(v, z)) % P == 0
        xy = [c*column(z), c*column([a*b % P for a, b in zip(z, theta)])]
        tracks.append([[int(value[0]) for value in vec.tolist()] for vec in xy])

    def triple(x, y, z):
        return sum(x[i]*y[j]*z[k] for i, j, k in permutations(range(5), 3)) % P

    cubic = []
    for i, j, k in combinations_with_replacement(range(2), 3):
        x, y, z = (tracks[h] for h in (i, j, k))
        cubic.append([sum(triple(x[a], y[b], z[c]) for a, b, c in product(range(2), repeat=3)
                          if a+b+c == degree) % P for degree in range(4)])
    assert matrix(cubic).det() == 25

    quartics = []
    for inputs in combinations_with_replacement(range(2), 4):
        coeff = nmod_poly([], P)
        for positions in permutations(range(5), 4):
            term = nmod_poly([1], P)
            for i, j in zip(inputs, positions):
                term *= nmod_poly([tracks[i][1][j], tracks[i][0][j]], P)
            coeff += term
        quartics.append(coeff)
    assert [int(poly[4]) for poly in quartics] == [21, 12, 14, 15, 7]
    assert reduce(lambda a, b: a.gcd(b), quartics) == nmod_poly([1], P)
    print('Cubic determinant modulo 31 is 25; the five polarized quartics have gcd one.')


if __name__ == '__main__':
    main()
