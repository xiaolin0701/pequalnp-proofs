"""Check the integer identity and the matching lemma in ThreeByThreeDirections.md."""
from itertools import combinations, permutations, product
import sympy as s

x, y, z = s.symbols("x y z")
idx = range(3)


def block(i, t):
    j, k = [a for a in idx if a != i]
    M = s.zeros(3)
    M[j,j], M[j,k] = t-1, t*(t-1)
    M[k,j], M[k,k] = t+1, -t*(t+1)
    return M


V = [block(i, t) for i, t in enumerate((x, y, z))]
q = [sum(A[i,j]*B[k,l] for i,j,k,l in product(idx, repeat=4) if i!=k and j!=l)
     for A,B in combinations(V, 2)]
c = sum(s.prod(V[p[i]][i,w[i]] for i in idx)
        for p in permutations(idx) for w in permutations(idx))

# Integer polynomial certificate. The multiplier of c (rather than c/2) is d.
a = 2*x*z**3+x*z**2-5*x*z-4*x-4*y*z**4+5*y*z**3+y*z**2-2*y*z-16*z**3+10*z**2+16*z
b = -(3*x*y**2+2*x*y*z**2-4*x*y*z+x*y+4*x+3*y**3-6*y**2*z**2+2*y**2*z+6*y**2+2*y*z**2-25*y*z-15*y-2*z**2-3*z)
h = -(3*x**3+3*x**2*y-11*x**2*z+3*x**2+4*x*y*z**2-5*x*y*z+2*x*y-6*x*z**2-5*x*z-x+4*y*z**2-3*y*z-3*y-6*z-11)
d = x*z**2-3*x*z-x-y*z**2+3*y*z+y+2*z**2+2
assert s.expand(a*q[0]+b*q[1]+h*q[2]+d*c-24*(z**3-z)) == 0
print("Verified polynomial identity over the integers: 24(z^3-z).")

# Enumerate every labelled rank pattern and every possible adjacency matrix.
# None denotes that all three vertices on that side have rank two.
checked = {}
for low_row, low_col in product((None, 0, 1, 2), repeat=2):
    count = 0
    for mask in range(1 << 9):
        edge = lambda i, j: bool(mask & (1 << (3*i+j)))
        row_deg = [sum(edge(i, j) for j in idx) for i in idx]
        col_deg = [sum(edge(i, j) for i in idx) for j in idx]
        if any((deg > 2 if i == low_row else deg != 1) for i, deg in enumerate(row_deg)):
            continue
        if any((deg > 2 if j == low_col else deg != 1) for j, deg in enumerate(col_deg)):
            continue
        if low_row is not None and low_col is not None and not edge(low_row, low_col):
            continue
        assert any(all(edge(i, m[i]) for i in idx) for m in permutations(idx))
        count += 1
    assert count > 0
    key = (low_row is not None, low_col is not None)
    checked[key] = checked.get(key, 0) + count
print("Matching verified for all feasible labelled graphs:", checked)
