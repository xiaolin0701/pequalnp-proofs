"""Check the four matching equations on the eleven-parameter GF(4) family."""

from functools import reduce
from itertools import combinations


def mul(a, b):
    # GF(4) elements a0+a1*T, reduced modulo T^2+T+1.
    product = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
    return product ^ 7 if product & 4 else product


class Poly(dict):
    # A monomial has one four-bit exponent per parameter. Degree is at most five.
    def __add__(self, other):
        result = Poly(self)
        for monomial, coefficient in other.items():
            value = result.get(monomial, 0) ^ coefficient
            if value:
                result[monomial] = value
            else:
                result.pop(monomial, None)
        return result

    def __mul__(self, other):
        result = Poly()
        for a, x in self.items():
            for b, y in other.items():
                monomial = a + b
                value = result.get(monomial, 0) ^ mul(x, y)
                if value:
                    result[monomial] = value
                else:
                    result.pop(monomial, None)
        return result


def constant(a):
    return Poly({0: a}) if a else Poly()


def total(items):
    return sum(items, Poly())


def elementary(items, degree):
    return total(reduce(Poly.__mul__, group, constant(1))
                 for group in combinations(items, degree))


def rank(rows):
    matrix = [list(row) for row in rows]
    pivot = 0
    for col in range(len(matrix[0])):
        found = next((i for i in range(pivot, len(matrix)) if matrix[i][col]), None)
        if found is None:
            continue
        matrix[pivot], matrix[found] = matrix[found], matrix[pivot]
        a = matrix[pivot][col]
        inverse = next(x for x in range(1, 4) if mul(a, x) == 1)
        matrix[pivot] = [mul(x, inverse) for x in matrix[pivot]]
        for i in range(pivot + 1, len(matrix)):
            a = matrix[i][col]
            matrix[i] = [x ^ mul(a, y) for x, y in zip(matrix[i], matrix[pivot])]
        pivot += 1
    return pivot


def main():
    v, u, w = (1, 1, 1, 1, 0), (1, 1, 0, 0, 0), (1, 2, 3, 0, 0)
    indices = range(5)
    h_basis = [tuple(int(j == k or j == 4) for j in indices) for k in range(4)]
    parameters = [Poly({1 << (4 * k): 1}) for k in range(11)]
    b = [parameters[0] * constant(x) for x in v]
    c = [parameters[1] * constant(x) + parameters[2] * constant(y) for x, y in zip(v, w)]
    d = [[total(parameters[3 + 4 * p + k] * constant(mul(left[i], h[j]))
                for p, left in enumerate((v, u)) for k, h in enumerate(h_basis))
          for j in indices] for i in indices]
    linear_coordinates = b + c + [entry for row in d for entry in row]
    assert rank([[p.get(key, 0) for p in linear_coordinates] for t in parameters for key in t]) == 11
    assert not total(b) and not total(c)
    assert all(not total(row) for row in d) and all(not total(col) for col in zip(*d))

    def contract(x, y):
        return total(x[i] * d[i][j] * y[j] for i in indices for j in indices)

    db, dc = elementary(b, 2), elementary(c, 2)
    contraction = contract(b, c)
    r2 = total(d[i][j] * d[k][l] + d[i][l] * d[k][j]
               for i, k in combinations(indices, 2) for j, l in combinations(indices, 2))
    equations = [
        r2 + db + dc,
        contraction,
        db * dc,
        db * elementary(c, 3) + elementary(b, 3) * dc + (db + dc) * contraction
        + contract([x * x * x for x in b], c) + contract(b, [x * x * x for x in c]),
    ]
    assert all(not equation for equation in equations), equations
    print("GF(4) column rank 11; zero row and column margins; all four formal polynomials vanish.")


if __name__ == "__main__":
    main()
