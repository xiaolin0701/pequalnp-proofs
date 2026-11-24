"""Exact Gram and permanent identities in CenteredEqualDegeneratePair.md."""

import itertools

import sympy as sp


lam = sp.symbols("lam")
first = sp.I / 20
minor = (sp.Rational(1, 20) * (sp.Rational(4, 75) + 4*lam**2/3)
         - (sp.Rational(1, 25) - 4*first*lam)**2)
assert sp.expand(minor - sp.Rational(8, 75)*(lam-first)*(lam+sp.I/5)) == 0

# The fourth roots leave only five terms in a multilinear five-row expansion.
unit = (1, 0, 0, 0, 0)
fourier = (0, 1, sp.I, -1, -sp.I)
ones = (1, 1, 1, 1, 1)
weight = 24 * sp.prod(fourier[1:])
for top_choice in itertools.product((0, 1), repeat=4):
    top_rows = [(unit, fourier)[i] for i in top_choice]
    count_units = top_choice.count(0)
    for bottom in (unit, fourier, ones):
        rows = [*top_rows, bottom]
        permanent = sum(sp.prod(rows[i][j] for i, j in enumerate(cols))
                        for cols in itertools.permutations(range(5)))
        nonzero = ((count_units == 0 and bottom in (unit, ones))
                   or (count_units == 1 and bottom == fourier))
        assert permanent == (weight if nonzero else 0)
print("Centered equal-pair Gram minor and all 48 multilinear permanent terms passed.")
