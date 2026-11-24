"""Complete the simultaneous-five-cycle case, ruling out dimension eight.

Use after verify_simultaneous_cycle.py. That proof reduces any remaining
eight-plane to four two-dimensional nontrivial character spaces U1,...,U4.
The search for these planes is projective over Z[zeta5]: use the product
of the four Grassmannians and impose the permanent equations. Consequently
a complex solution would give one over an algebraic closure of F311 with
zeta5 mapping to 6. The script uses SymPy to generate finite-field equations
and Singular to compute a zero-dimensional coordinate algebra; allow several
minutes for the largest reduction.

Let F(x) be the circulant permanent. If all adjacent pairs of coordinate
forms on U1 are dependent, its active coordinates cannot form a connected
subset of the five-cycle (or all nonzero forms would be proportional).
At least two must then vanish. But F=0 contains no line supported on just
three coordinates. The affine group of indices is transitive on triples
via their complementary pair. We check one triple in all three RREF charts.
Thus an offset translation takes U1 to the chart with pivot columns 0,1.

A weight-a vector is T_ij=zeta5^(ai) x_(j-i). The third derivative at J
with weights a,a,-2a defines a trilinear tensor, computed directly from
permutations below. For a basis x,y of U_a its evaluations on x,x; x,y; y,y
give a three-by-five matrix K with U_(-2a) in the kernel. For any four
columns of K, its signed three-minors form a kernel vector on those columns.
This vector belongs to U_(-2a): for rank three the kernel has dimension two,
and at lower rank the vector is zero.

In the main chart F vanishes on U1; there are 2860 solutions counted with
multiplicity over the algebraic closure. Requiring F to vanish on just the
first two displayed minor vectors cuts the degree to 74 and then to 2.
We check two distinct explicit points of this remaining system. Therefore
they exhaust its points over the algebraic closure. At each, the tensors
force U3 and then U4 uniquely. The quadratic mixed coefficient on weights
1,4 is nonzero, excluding the two final planes. Specifically, apart from
a nonzero factor the coefficient is x.y - sum(x)sum(y) - Fx*Fy, with
Fx=sum_i zeta5^(-i)x_i, Fy=sum_j zeta5^j y_j. This is the all-ones Hessian,
computed by excluding coinciding rows and columns.
"""
import argparse
import itertools
import subprocess
from math import prod
from sympy import GF
from sympy.polys.rings import ring

from verify_simultaneous_cycle import coefficients, PERMS, P

_, *VARIABLES = ring("a,b,c,d,e,f", GF(P))
ROOT = 6
F = coefficients()[5]


def format_poly(g):
    if not hasattr(g, "terms"):
        return str(g % P)
    def mon(m):
        return "*".join(c if e == 1 else c+"^"+str(e) for c,e in zip("abcdef",m) if e)
    return "+".join(str(int(v)%P)+("*"+mon(m) if sum(m) else "") for m,v in g.terms()) or "0"


def plane(pivots, positions):
    U = [[int(i==p) for i in range(5)] for p in pivots]
    variables = iter(VARIABLES)
    for row, pivot in zip(U,pivots):
        for j in positions:
            if j > pivot and j not in pivots:
                row[j] = next(variables)
    return U


def f(x):
    return sum(c*prod(x[i] for i in ind) for ind,c in F.items())


def pencil(x,y):
    return [f([a+t*b for a,b in zip(x,y)]) for t in range(5)]+[f(y)]


def tensor(a):
    T = [[[0]*5 for _ in range(5)] for _ in range(5)]
    for permutation in PERMS:
        cells = [(j-i)%5 for i,j in enumerate(permutation)]
        for i,j,k in itertools.permutations(range(5),3):
            T[cells[i]][cells[j]][cells[k]] += pow(ROOT,a*(i+j-2*k)%5,P)
    return [[[v%P for v in row] for row in plane] for plane in T]


def constraints(U,a):
    T = tensor(a)
    return [[sum(x[i]*y[j]*T[i][j][k] for i,j in itertools.product(range(5),repeat=2))
             for k in range(5)] for x,y in itertools.combinations_with_replacement(U,2)]


def det3(M,cols):
    a,b,c=([r[i] for i in cols] for r in M)
    return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))


def minors(M):
    for cols in itertools.combinations(range(5),4):
        v=[0]*5
        for i,j in enumerate(cols):
            v[j]=(-1)**i*det3(M,cols[:i]+cols[i+1:])
        yield v


def solve(path, script, expected):
    script="ring r=311,(a,b,c,d,e,f),dp;\n"+script+"\nexit;\n"
    proc=subprocess.run([path,"-q"],input=script,text=True,stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,check=True)
    if proc.stdout.strip() != expected:
        raise RuntimeError(proc.stdout)


def certify_charts(path):
    for pivots in itertools.combinations(range(3),2):
        U=plane(pivots,range(3))
        solve(path,"ideal I="+",".join(map(format_poly,pencil(*U)))
              +";print(std(I)[1]);","1")
    U=plane((0,1),range(5))
    script="ideal I="+",".join(map(format_poly,pencil(*U)))+";ideal J=std(I);print(vdim(J));\n"
    for j,v in enumerate(itertools.islice(minors(constraints(U,1)),2)):
        names=["v"+str(j)+str(k) for k in range(5)]
        script+="".join("poly "+n+"="+format_poly(x)+";\n" for n,x in zip(names,v))
        terms=[]
        for ind,c in F.items():
            value="1"
            for i in ind:
                value="reduce(("+value+")*"+names[i]+",J)"
            terms.append(str(c)+"*"+value)
        script+="poly q"+str(j)+"="+"+".join(terms)+";\nJ=std(J+q"+str(j)+");print(vdim(J));\n"
    solve(path,script,"2860\n74\n2")


def kernel(M):
    m=[[v%P for v in row] for row in M]
    pivots=[]
    for j in range(5):
        k=len(pivots)
        i=next((i for i in range(k,len(m)) if m[i][j]),None)
        if i is None:
            continue
        pivots.append(j)
        m[k],m[i]=m[i],m[k]
        inv=pow(m[k][j],-1,P)
        m[k]=[v*inv%P for v in m[k]]
        for i in range(len(m)):
            if i!=k:
                m[i]=[(v-m[i][j]*w)%P for v,w in zip(m[i],m[k])]
    return [[int(i==free) if i not in pivots else -m[pivots.index(i)][free]%P for i in range(5)]
            for free in range(5) if free not in pivots]


def exclude_remaining():
    examples=[[[1,0,0,259,0],[0,1,95,0,0]],[[1,0,0,0,275],[0,1,0,305,0]]]
    for U in examples:
        assert all(t%P==0 for t in pencil(*U))
        M=constraints(U,1)
        assert all(f(v)%P==0 for v in itertools.islice(minors(M),2))
        V=kernel(M)
        assert len(V)==2
        W=kernel(constraints(V,3))
        assert len(W)==2
        x,y=U[0],W[0]
        fx=sum(v*pow(ROOT,-i,P) for i,v in enumerate(x))
        fy=sum(v*pow(ROOT,i,P) for i,v in enumerate(y))
        pair=sum(a*b for a,b in zip(x,y))-sum(x)*sum(y)-fx*fy
        assert pair%P!=0


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--singular",default="Singular")
    path=parser.parse_args().singular
    exclude_remaining()
    certify_charts(path)
    print("The chart degrees are 2860, 74, and 2. Both remaining opposite pairings are nonzero.")
    print("Every simultaneously cyclically stable five-by-five complex level space has dimension <= 7.")
