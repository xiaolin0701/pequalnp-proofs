"""Exclude every linear 4-plane in the F13 quotient cone for seed D2.

Needs Python, python-flint and Singular. The slice is recomputed from scratch.
"""
import argparse
import random
import re
import string
import subprocess
import tempfile
from math import prod
from pathlib import Path
from flint import fmpz_mod_poly_ctx, fq_default_ctx
from verify_rectangular_seed_extensions import (
    P, cyclotomic_seed, expand, product_coefficient, quotient,
)

NAMES = string.ascii_lowercase[:10]
CUTS = [
    [3,7,7,2,5,2,6,2,4,10],
    [8,6,9,10,4,6,1,10,10,0],
    [6,6,11,6,3,10,3,7,11,9],
    [3,8,6,12,2,8,6,3,1,4],
]


def setup():
    rank, directions = quotient(cyclotomic_seed, (0,2,3))
    assert rank == 7 and len(directions) == 10
    definitions = []
    for i in range(20):
        form = "+".join(str(v[i])+"*"+name for name,v in zip(NAMES,directions) if v[i])
        definitions.append("poly v"+str(i)+"="+(form or "0")+";")
    rng = random.Random(473)
    points = [(0,0,0)] + [tuple(rng.randrange(P) for _ in range(3)) for _ in range(13)]
    equations = set()
    for point in points:
        shifted = [1+entry for entry in cyclotomic_seed(*point)]
        for degree in (2,3,4):
            equations.add(product_coefficient(shifted, degree))
    definitions.append("ideal I="+",".join(sorted(equations))+";")
    return definitions


def parse_sparse(expression):
    terms = []
    for sign,term in re.findall(r"([+-]?)([^+-]+)", expression):
        coefficient = -1 if sign=="-" else 1
        exponents = []
        for item in term.split("*"):
            if item.isdigit():
                coefficient *= int(item)
            else:
                variable,*power = item.split("^")
                exponents.append((NAMES.index(variable), int(power[0]) if power else 1))
        terms.append((coefficient, exponents))
    return terms


def evaluate(poly, point):
    return sum((c*prod(point[i]**n for i,n in monomial) for c,monomial in poly), point[0]*0)


def gradient(poly, point):
    result = [point[0]*0 for _ in point]
    for c,monomial in poly:
        for i,k in monomial:
            result[i] += c*k*prod(point[j]**(n-int(j==i)) for j,n in monomial)
    return result


def nullspace(rows, field):
    work = [row[:] for row in rows]
    pivots = []
    for j in range(len(NAMES)):
        level = len(pivots)
        index = next((i for i in range(level,len(work)) if not work[i][j].is_zero()), None)
        if index is None:
            continue
        work[index],work[level] = work[level],work[index]
        inverse = 1/work[level][j]
        work[level] = [x*inverse for x in work[level]]
        for i,row in enumerate(work):
            if i!=level and not row[j].is_zero():
                coefficient = row[j]
                work[i] = [x-coefficient*y for x,y in zip(row,work[level])]
        pivots.append(j)
        if len(pivots)==len(work):
            break
    basis = []
    for j in range(len(NAMES)):
        if j in pivots:
            continue
        vector = [field(0) for _ in NAMES]
        vector[j] = field(1)
        for i,k in enumerate(pivots):
            vector[k] = -work[i][j]
        basis.append(vector)
    return basis


def read_point(equations, degree):
    # The first equation is for the separating coordinate j, the rest provide
    # affine-linear lifts successively in i,h,...,a. Every point is rechecked.
    modulus_coeffs = [0]*(degree+1)
    for c,monomial in parse_sparse(equations[0]):
        assert not monomial or len(monomial)==1 and monomial[0][0]==9
        exponent = monomial[0][1] if monomial else 0
        modulus_coeffs[exponent] += c
    modulus = fmpz_mod_poly_ctx(P)(modulus_coeffs)
    assert modulus.degree()==degree and modulus.is_irreducible()
    if degree==1:
        field = fq_default_ctx(P,1)
        root = field(-modulus_coeffs[0])/field(modulus_coeffs[1])
    else:
        field = fq_default_ctx(modulus=modulus)
        root = field.gen()
    point = [field(0) for _ in NAMES]
    point[-1] = root
    for k,expression in enumerate(equations[1:],start=1):
        poly = parse_sparse(expression)
        j = 9-k
        constant = evaluate(poly,point)
        point[j] = field(1)
        coefficient = evaluate(poly,point)-constant
        point[j] = -constant/coefficient
    assert all(evaluate(parse_sparse(f),point).is_zero() for f in equations)
    return tuple(int(n)%P for n in modulus_coeffs),field,point


def run(singular):
    definitions = setup()
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        polys = [parse_sparse(f) for f in expand(singular,folder,NAMES,definitions,["I"])]
        cuts = ["+".join(str(c)+"*"+n for c,n in zip(row,NAMES)) for row in CUTS]
        instructions = [
            "ring r=13,("+",".join(NAMES)+"),dp;", *definitions,
            'LIB "primdec.lib";', "short=0;", "ideal cut="+",".join(cuts)+";",
            "ideal slice=I,cut[1],cut[2],cut[3],cut[4]-1;", "ideal G=std(slice);",
            "dim(G);", "vdim(G);", "dim(std(I+cut));",
            "list ptsList=minAssGTZ(G);", "size(ptsList);",
            "for(int i=1;i<=size(ptsList);i++){vdim(std(ptsList[i]));ptsList[i];}",
        ]
        path = folder/"slice.sing"
        path.write_text("\n".join(instructions))
        output = subprocess.run([singular,"-q",str(path)],check=True,text=True,
                                stdout=subprocess.PIPE).stdout.splitlines()
    dimension,length,infinity,number = map(int,output[:4])
    assert (dimension,length,infinity,number)==(0,24,0,6)
    assert len(output)==4+number*11
    degrees = []
    moduli = set()
    for group in range(number):
        start = 4+group*11
        degree = int(output[start])
        triangular = [line.split("=",1)[1] for line in output[start+1:start+11]]
        modulus,field,point = read_point(triangular,degree)
        assert modulus not in moduli
        moduli.add(modulus)
        assert all(evaluate(poly,point).is_zero() for poly in polys)
        assert [sum(c*x for c,x in zip(cut,point)) for cut in CUTS] == \
               [field(0),field(0),field(0),field(1)]
        jacobian = [gradient(poly,point) for poly in polys]
        basis = nullspace(jacobian,field)
        assert len(basis)==4
        direction = [sum(c*x for c,x in zip((10,0,6,8),column)) for column in zip(*basis)]
        assert all(sum(a*b for a,b in zip(row,direction)).is_zero() for row in jacobian)
        assert any(not evaluate(poly,direction).is_zero() for poly in polys)
        degrees.append(degree)
    assert sorted(degrees)==[1,1,2,3,5,12] and sum(degrees)==length
    print("Affine slice length 24; homogeneous fourth cut meets the cone only at 0.")
    print("Residue degrees and tangent dimensions:", [(d,4) for d in sorted(degrees)])
    print("Each tangent space contains the stated direction outside the cone.")


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular",default="Singular")
    run(parser.parse_args().singular)
