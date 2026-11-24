"""Verify the small-support exclusions for the five-root column Gram matrix."""

import argparse
import shutil
import subprocess

from check_five_planar_one_axis import geometry


def sparse_scales():
    source=geometry(False)
    source.extend("""
        // Three active lambda coordinates; positions 1,2 denote its two zeros.
        poly g3=C[1,2];
        int a,d;
        poly obstruction;
        for(a=3;a<=5;a++){for(d=a+1;d<=5;d++){
            obstruction=C[a,a]*C[d,1]*C[d,2]+C[d,d]*C[a,1]*C[a,2]
                -C[a,d]*(C[a,2]*C[d,1]+C[a,1]*C[d,2]);
            g3=gcd(g3,obstruction);
        }}
        if(deg(g3)!=0){ERROR("the three-coordinate Schur identities have a common scale");}

        // Four active coordinates; the sole zero is at position 1.
        matrix M[6][4];int n=0;poly factor;poly units=t;
        for(a=2;a<=5;a++){units=units*C[1,a]*C[a,a];}
        for(a=2;a<=5;a++){for(d=a+1;d<=5;d++){
            n++;
            factor=C[1,a]*C[d,d]*C[1,d]*C[a,a];
            M[n,a-1]=factor-C[a,d]*C[1,d]^2*C[a,a];
            M[n,d-1]=factor-C[a,d]*C[1,a]^2*C[d,d];
        }}
        ideal minors=minor(M,4);
        poly g4=minors[1];
        for(a=2;a<=size(minors);a++){g4=gcd(g4,minors[a]);}
        if(g4==0){ERROR("the six-by-four matrix never has full column rank");}
        poly divisor=gcd(g4,units);
        while(deg(divisor)>0){g4=g4/divisor;divisor=gcd(g4,units);}
        if(deg(g4)!=0){ERROR("the four-coordinate case has an exceptional scale");}
        "ok";
    """.splitlines())
    return source


def exceptional_diagonal():
    source=[
        line.replace("(s,z,f,h)","(s,z,f,h,d)")
        .replace("minpoly=r^4+r^3+r^2+r+1;", "minpoly=r^8-r^7+r^5-r^4+r^3-r+1;")
        .replace("poly t=-1;", "number t=(1+(1+2*(r^3+r^12))*(1+2*r^5))/4;"
                 'if(2*t^2-t+2!=0){ERROR("wrong root");}')
        .replace("b[i,1]=r^(i-1)", "b[i,1]=r^(3*(i-1))")
        for line in geometry(True)
    ]
    source.extend("""
        matrix mu[5][1];mu[2,1]=1;mu[3,1]=s;mu[4,1]=z;mu[5,1]=f;
        matrix K[5][5];K[1,1]=d;
        for(i=1;i<=5;i++){for(j=1;j<=5;j++){if(i!=1 || j!=1){
            if(C[i,j]==0){ERROR("additional zero matrix entry");}
            K[i,j]=(mu[i,1]+mu[j,1])/C[i,j];
        }}}
        ideal equations=minor(K,3),h*s*z*f-1;
        option(redSB);ideal gb=std(equations);
        if(size(gb)!=1 || gb[1]!=1){ERROR("expected a unit ideal at the exceptional diagonal");}
        "ok";
    """.splitlines())
    return source


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular",default="Singular")
    binary=shutil.which(parser.parse_args().singular)
    if not binary:
        parser.error("Singular executable missing")
    for title,source in (("three and four nonzero Gram parameters",sparse_scales()),
                         ("four nonzero parameters with a zero diagonal coefficient",exceptional_diagonal())):
        result=subprocess.run([binary,"-q"],input="\n".join(source+["quit;"]),
                              capture_output=True,text=True,check=True)
        if result.stdout.strip()!="ok" or result.stderr.strip():
            raise ArithmeticError(result.stdout[:1500]+result.stderr[:1500])
        print(f"Verified {title}.")


if __name__=="__main__":
    main()
