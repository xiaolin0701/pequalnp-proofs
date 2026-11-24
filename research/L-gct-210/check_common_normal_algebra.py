"""Verify an exact algebra-rank witness for CommonRowColumnNormals.md.

Uses Python 3 and SymPy. All matrices in this computation have rational entries.
"""
from sympy import Matrix, diag, eye, ones


def witness():
    normal = Matrix([1, 2, 3, 4, 5])
    unit = ones(5, 1)
    basis = Matrix.hstack(*normal.T.nullspace())
    pure_directions = Matrix.vstack(unit.T, normal.T).nullspace()
    gram = basis.T * (unit * unit.T - eye(5)) * basis
    generators = []
    for direction in pure_directions:
        mixed = direction * unit.T + unit * direction.T - 2 * diag(*direction)
        generators.append(gram.inv() * basis.T * mixed * basis)
    words = [
        (), (0,), (1,), (2,), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2),
        (2, 0), (2, 1), (2, 2), (0, 0, 1), (0, 0, 2), (0, 1, 1),
    ]
    columns = []
    for word in words:
        matrix = eye(4)
        for index in word:
            matrix = matrix * generators[index]
        columns.append(matrix.reshape(16, 1))
    determinant = Matrix.hstack(*columns).det()
    assert gram.det() == 5 and determinant != 0
    print(f"Gram determinant = {gram.det()}")
    print(f"Determinant of the sixteen algebra elements = {determinant}")


if __name__ == "__main__":
    witness()
