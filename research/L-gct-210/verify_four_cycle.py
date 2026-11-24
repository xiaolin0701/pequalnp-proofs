"""The L-gct-210 bound holds for a space stable under a four-cycle of its rows.

A cyclic character of weight a=1,2,3 has its first four rows i^ra x and its
last row zero (i is a primitive fourth root). Weight zero has four identical
rows u and a last row v. For rank-one perturbations u_j tensor v_j, the mixed
kth permanent coefficient at J is (5-k)! times the product of the two sums
of products over k distinct indices, one sum for the row factors and one for
the column factors. This follows by extending each injection pair to a
permutation in (5-k)! ways. Multiplicities of repeated directions do not
affect the vanishing statements in characteristic zero.

Write E_a for the column-vector space of the weight-a part, a!=0. Its fourth
coefficient forces e4(x)=0 (e_k denotes the elementary symmetric polynomial).
A subspace E with common missing coordinates and e4=0 has at most three active
coordinates, by the product of its four remaining linear coordinate forms.
If it has full support, the identity is sum_j 1/x_j=0 in its rational
function field. Group the nonzero coordinate forms up to proportionality.
Every group has at least two members: multiplying by the product of distinct
representative forms and reducing modulo one of them gives the vanishing of
the sum of reciprocal coefficients in that group. Thus dim E<=2. When dim E=2,
the full-support case has two groups of sizes 2 and 3. On the kernel of the
three-member group's form, some vector has exactly two nonzero coordinates.
The additional weight-2 equation e2(x)=0 rules this out. On three coordinate
positions e2 is nondegenerate, hence has no isotropic plane. Thus dim E2<=1.

If dim E1=3 it is the full coordinate space on a triple S. Mixed weights
1,1,2 on distinct indices force sum_{k!=i,j} z_k=0 for z in E2 and distinct
i,j in S. Write z on S as (c,c,c), on the complement as (u,v); then u+v=-c.
The equations e2(z)=e4(z)=0 give uv=0 and c=0, hence z=0. The mixed pair 1,3
forces y in E3 to have values (b,b,b) on S and (r,s) on its complement with
r+s=-2b. The mixed coefficient 1,1,3,3 forces b(r+s)+rs=0, i.e. rs=2b^2.
Then e4(y)=3b^2rs+b^3(r+s)=4b^4, so b=r=s=0. Thus a three-dimensional
E1 or E3 leaves the other nonzero weights trivial. The script checks the
row factors used in these mixed equations have nonzero residues modulo 13.

In weight zero, the image of u has dimension <=1. Otherwise two coordinates
can simultaneously cancel the ones, leaving four identical rows supported in
at most three columns. If u is nonzero, its nonzero coordinates have distinct
values by the same argument after scaling. For every purely last-row direction
w, expansion in that row forces sum_j w_j product_{k!=j}(1+t u_k)=0. The
polynomials indexed by different values of u_j are linearly independent,
by partial fractions, including the possible value zero. Hence the fixed
space has dimension <= 1+5-#distinct(u_j), at most four. The alternative
u=0 also has dimension at most four since its last row has zero sum.

A nine-plane would therefore have dimensions (4,2,1,2). If the fixed
space consists entirely of last-row directions, it is the whole sum-zero
last row. Adding e_j-e_k in that row shows that all deleted permanents for
the remaining four rows are equal; on each nonzero-weight space their sum
is 120 and therefore each is 24. Thus E1,E3 each have at most three active
coordinates (their top coefficients on every set of four columns vanish).
For x in E1 and y in E3 the second-order equations on each set of four are
sum_{i!=j, i,j!=k} x_i y_j=0. Denote the coordinate sums by X,Y. Summing
and subtracting gives (2x_k-X)(2y_k-Y)=XY. If X and Y are nonzero linear
forms, fix a y with Y!=0; for each k this identity forces x_k proportional
to X. That contradicts dim E1=2. Otherwise, assume X=0 by symmetry. The
two-dimensional centered space E1 has at least three active positions, at
each of which y_k=Y/2. If Y is nonzero, E3 already has three active positions
and summing gives Y=3Y/2. Thus Y=0, and the only possible y live on the
remaining at most two positions and have sum zero, contradicting dim E3=2.

The other fixed four-plane has a nonzero first-row projection u. The distinct
value count shows u has just one nonzero coordinate, normalized at column 4.
The pure last-row kernel is exactly the centered subspace on columns 0..3.
The permanent identity along a lift with column-4 parameter z gives
(1+z)*sum_{j<4}(1+z v_j)+(1+z v_4)=5, hence sum_{j<4}v_j=0 and v_4=-4.
Subtract the centered last-row part. The affine fixed slice now has first
four rows (1,1,1,1,1+z) and last row (1+c_0,...,1+c_3,1-4z), sum(c)=0.
At each such point, E1 and E3 annihilate each other under the Hessian.
Deleting any two distinct first-four rows gives the same 3-by-3 permanent,
and the total opposite-character row factor is -4. The code uses the
corresponding 5-by-5 pairings after division by -4. For a two-row basis U
of E1, all stacked rows U M must have common annihilator E3 of dimension 2.
All 4-by-4 minors must vanish. In every one of the ten RREF charts, Singular
verifies an exact rational polynomial combination of these minors equal to 1.
This excludes the final case.
"""
import argparse
import itertools
import subprocess
from math import prod

PERMS = list(itertools.permutations(range(5)))


def check_factors():
    # 5 is a primitive fourth root modulo 13.
    for weights in ((2,2),(1,3),(1,1,2),(1,1,3,3),(1,1,1,1),(2,2,2,2)):
        value = sum(pow(5, sum(i*a for i,a in zip(indices, weights)),13)
                    for indices in itertools.permutations(range(4),len(weights)))
        assert value % 13


def pairing(c,z):
    m = [[1]*4+[1+z]]*4 + [[1+x for x in c]+[1-4*z]]
    gram = [[0]*5 for _ in range(5)]
    for p in PERMS:
        gram[p[0]][p[1]] += prod(m[i][p[i]] for i in range(2,5))
    return gram


def check(path):
    check_factors()
    c_choices = [[0]*4]+[[int(i==j)-int(i==3) for i in range(4)] for j in range(3)]
    forms = [pairing(c,z) for c,z in itertools.product(c_choices,(0,1))]
    for pivots in itertools.combinations(range(5),2):
        rows = [[str(int(j==p)) for j in range(5)] for p in pivots]
        variables = iter("abcdef")
        for row,p in zip(rows,pivots):
            for j in range(p+1,5):
                if j not in pivots:
                    row[j] = next(variables)
        entries = ["+".join(x+"*("+str(m[i][j])+")" for i,x in enumerate(row))
                   for m in forms for row in rows for j in range(5)]
        script = ("ring r=0,(a,b,c,d,e,f),dp;\nmatrix H[16][5]="+",".join(entries)
                  +";\nideal I=minor(H,4);\nmatrix M=lift(I,ideal(1));\n"
                  +'matrix T=matrix(I)*M;\nif(T[1,1]==1){print("CERTIFIED");}\nexit;\n')
        result = subprocess.run([path,"-q"],input=script,text=True,stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,check=True)
        if result.stdout.strip() != "CERTIFIED":
            raise RuntimeError(result.stdout)
    print("Four-row cycle: all ten two-plane charts ruled out by exact rational identities.")
    print("The complex level space has dimension <= 8.")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--singular",default="Singular")
    check(p.parse_args().singular)
