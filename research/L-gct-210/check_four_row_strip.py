"""Symbolically check the row-strip coefficients and the last pencil cases."""
from itertools import combinations, permutations
import sympy as sp


def elementary(values, degree):
    return sum((sp.prod(term) for term in combinations(values, degree)), sp.S.Zero)


def permanent(matrix):
    return sum(sp.prod(matrix[i, j] for i, j in enumerate(sigma))
               for sigma in permutations(range(matrix.rows)))


g = sp.symbols("g0:5")
s = sum(g)
# Dividing by e2=e3=e4, with elementary symmetric polynomial reduction,
# checks the dot products on the whole stated family.
for expression in [
    sum(x**2-s*x for x in g), sum(x**3-s*x**2 for x in g),
    sum((x**2-s*x)**2 for x in g),
    sum((x**2-s*x)*(x**3-s*x**2) for x in g)-5*sp.prod(g)
]:
    sym, rem, substitutions = sp.symmetrize(expression, g, formal=True)
    assert rem == 0
    assert sym.subs({t:0 for t, _ in substitutions[1:4]}) == 0

eye = sp.eye(5)
one = sp.ones(5, 1)
first = sp.Matrix.hstack(*(2*eye[:,i]-one for i in range(4)))
second = sp.Matrix.hstack(*(eye[:,i]+eye[:,4] for i in range(4)))
q = eye-sp.ones(5)/4
cross = first.T*q*second
assert cross == 2*sp.eye(4)-sp.ones(4)/2 and cross.rank() == 3
print("Strip mixed inverse-Gram block has rank", cross.rank())

p = sp.symbols("p0:5")
u = sp.symbols("u0:4")
z = sp.Symbol("z")
# To keep all five row parameters and four column parameters independent
# while avoiding an unnecessary ninth-variable expansion, use multilinear
# interpolation: each parameter occurs at most once per monomial in each
# 4x4 permanent. The rank-one product formula below is also termwise.
for k in range(1,5):
    diff = elementary(p[1:],k) - elementary(p[:1]+p[2:],k)
    assert sp.expand(diff - (p[1]-p[0])*elementary(p[2:], k-1)) == 0
sample_p = sp.Matrix([1,2,-3,4,4])
sample_u = sp.Matrix([2,-1,3,5])
M = sp.ones(5,4) + z*sample_p*sample_u.T
c1 = permanent(M[1:,:])
c2 = permanent(M.extract([0,2,3,4],range(4)))
exact = sum(sp.factorial(k)*sp.factorial(4-k)*elementary(tuple(sample_u), k) *
            (sample_p[1]-sample_p[0])*elementary(tuple(sample_p)[2:],k-1)*z**k
            for k in range(1,5))
assert sp.expand(c1-c2-exact) == 0
print("All four deleted-row difference coefficients agree.")

b = sp.Matrix.hstack(*eye.columnspace()[:3])
row = (eye-sp.ones(5)/3)*b/2
assert row.rank()==3 and row[3,:]==row[4,:] and row[:3,:].T*sp.ones(3,1)==sp.zeros(3,1)
a,b,c,d = sp.symbols("a b c d")
p0 = (a,b,-a-b,d,d)
assert all(sp.expand((p0[1]-p0[0])*elementary(p0[2:],k-1))!=0 for k in (3,4))
p1 = (a,b,c,-a-b-c,0)
assert sp.expand((p1[1]-p1[0])*elementary(p1[2:],2))!=0
print("Both residual pencil parameterizations and their nonzero tests agree.")

# Check the cubic nodes, the e4 != 0 three-row Gram, and the Fourier residue.
node_hessian = sp.ones(4)-sp.eye(4)
assert node_hessian.det() == -3
T = (0,1,2)
v2 = sp.Matrix.hstack(*(one-eye[:,i]-eye[:,j] for i,j in combinations(T,2)))
outside = one-sum((eye[:,i] for i in T),sp.zeros(5,1))
assert v2.T*q*v2 == sp.eye(3)-sp.ones(3)/4
assert (eye[:,3].T*q*outside)[0] == sp.Rational(1,2)
x,y,z,t = sp.symbols("x y z t")
power_rows = [x, t*x, y, z, 0]
def coefficient_rows(k, powers):
    coords = [elementary(power_rows[:i]+power_rows[i+1:], k) for i in range(5)]
    return sp.Matrix(5,len(powers),lambda i,j:sp.Poly(coords[i],x,y,z).coeff_monomial(powers[j]))
left = coefficient_rows(2,[y*z,x*y,x*z])
right = coefficient_rows(3,[x*y*z,x*x*y,x*x*z])
cross = 2*left.T*q*right
target = sp.Matrix([[t+1,-t,-t],[(t-1)**2,t*(t+1),-t*(t+1)],
                    [(t-1)**2,-t*(t+1),t*(t+1)]])
assert any(sp.simplify(cross.extract(range(3),order)-target)==sp.zeros(3)
           for order in ((0,1,2),(0,2,1)))
assert cross.subs(t,1).rank()==cross.subs(t,-1).rank()==2
print("Zero-sum cubic node, three-row Gram and Fourier coefficient matrix agree.")

# Five distinct fifth roots in Q[z]/Phi5.
v = sp.Symbol("v")
cyclo = sp.Poly(v**4+v**3+v**2+v+1,v)
rows = []
for coeffs in [(3,5,7,11),(13,17,19,23)]:
    A,B,C,D = coeffs
    rows.append([sum((1+A,B,C,D)[k]*v**(i*k) for k in range(4)) for i in range(5)])
m = sp.Matrix([[v**i for i in range(5)]]*3 + rows)
value = sp.Poly(permanent(m),v).rem(cyclo).as_expr()
assert value == 30*(4*5*17-(1+3)*19-(1+13)*7)
print("Fourier obstruction agrees with the full fifth-order permanent.")
