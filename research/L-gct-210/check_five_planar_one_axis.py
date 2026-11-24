"""Check the one-axis inverse-Gram obstruction over the cyclotomic field Q(zeta_5)."""

import argparse
import shutil
import subprocess


def geometry(exceptional):
    variables = "(s,z,f,h)" if exceptional else "t"
    program = [
        f"ring R=(0,r),{variables},dp;",
        "minpoly=r^4+r^3+r^2+r+1;",
    ]
    if exceptional:
        program.append("poly t=-1;")
    program.extend("""
        matrix b[5][1]; matrix C[5][5]; int i,j,k,m;
        for(i=1;i<=5;i++){b[i,1]=r^(i-1);}
        for(i=1;i<=5;i++){for(j=1;j<=5;j++){
            C[i,j]=1+t*(b[i,1]+b[j,1])-4*t^2*b[i,1]*b[j,1];
            if(i==j){C[i,j]=C[i,j]-5;}
        }}
        matrix c[5][3];matrix theta[5][5];matrix x[5][3];matrix y[5][3];
        for(i=1;i<=3;i++){c[i+1,i]=b[5,1];c[5,i]=-b[i+1,1];}
    """.splitlines())
    return program


def cubic_coefficients():
    return """
        proc third(matrix u,matrix v,matrix w,int a,int b,int c){
            poly A=0;poly B=0;poly D=0;poly AB=0;poly BD=0;poly AD=0;poly ABD=0;int l;
            for(l=1;l<=5;l++){
                A=A+u[l,a];B=B+v[l,b];D=D+w[l,c];
                AB=AB+u[l,a]*v[l,b];BD=BD+v[l,b]*w[l,c];AD=AD+u[l,a]*w[l,c];
                ABD=ABD+u[l,a]*v[l,b]*w[l,c];
            }
            return(A*B*D-AB*D-BD*A-AD*B+2*ABD);
        }
        matrix T[10][4];int n=0;
        for(i=1;i<=3;i++){for(j=i;j<=3;j++){for(k=j;k<=3;k++){
            n++;
            T[n,1]=third(x,x,x,i,j,k);
            T[n,2]=third(y,x,x,i,j,k)+third(x,y,x,i,j,k)+third(x,x,y,i,j,k);
            T[n,3]=third(y,y,x,i,j,k)+third(x,y,y,i,j,k)+third(y,x,y,i,j,k);
            T[n,4]=third(y,y,y,i,j,k);
        }}}
    """.splitlines()


def generic_program():
    program = geometry(False)
    program.extend("""
        int pairs=0;
        for(i=1;i<=5;i++){for(j=i;j<=5;j++){for(k=i;k<=5;k++){for(m=k;m<=5;m++){
            if(i!=k || j<m){
                if(deg(gcd(C[i,j],C[k,m]))>0){ERROR("two Gram denominators have a common root");}
                pairs++;
            }
        }}}}
        if(pairs!=105){ERROR("expected 105 different pairs of entries");}
        poly den=1;
        for(i=2;i<=5;i++){den=den*C[1,i];}
        for(i=2;i<=5;i++){theta[i,i]=b[i,1]*(den/C[1,i]);}
        x=C*c;y=C*theta*c;
    """.splitlines())
    program.extend(cubic_coefficients())
    program.extend("""
        ideal I=minor(T,4);
        poly g=I[1];for(i=2;i<=size(I);i++){g=gcd(g,I[i]);}
        if(g==0){ERROR("all cubic minors vanish");}
        poly units=t*(1+t)*den;
        poly divisor=gcd(g,units);
        while(deg(divisor)>0){g=g/divisor;divisor=gcd(g,units);}
        if(deg(g)!=0){ERROR("an unsupported exceptional scale remains");}
        "ok";
    """.splitlines())
    return program


def endpoint_program(zero_gram=False):
    program = geometry(True)
    if zero_gram:
        # Q(zeta_15) contains zeta_5 and both roots of 2t^2-t+2.
        program = [
            line.replace("minpoly=r^4+r^3+r^2+r+1;", "minpoly=r^8-r^7+r^5-r^4+r^3-r+1;")
            .replace("poly t=-1;", "number t=(1+(1+2*(r^3+r^12))*(1+2*r^5))/4;"
                     'if(2*t^2-t+2!=0){ERROR("incorrect marked residual");}')
            .replace("b[i,1]=r^(i-1)", "b[i,1]=r^(3*(i-1))")
            for line in program
        ]
    program.extend("""
        theta[3,3]=1;theta[4,4]=s;theta[5,5]=z;
        x=C*c;y=C*theta*c;
    """.splitlines())
    program.extend(cubic_coefficients())
    program.extend("""
        poly invert=h*s*z*(s-1)*(z-1)*(z-s)-1;
        option(redSB);
        ideal Ic=minor(T,4),invert,f;
        ideal Gc=std(Ic);
        if(size(Gc)!=1 || Gc[1]!=1){ERROR("the cubic saturation is not the unit ideal");}
        // The row-axis classification fixes a different affine origin.
        for(i=2;i<=5;i++){theta[i,i]=theta[i,i]+f;}
        y=C*theta*c;
        matrix F[15][1];int l,a1,a2,a3,a4;poly val;int count=0;
        for(i=1;i<=3;i++){for(j=i;j<=3;j++){for(k=j;k<=3;k++){for(l=k;l<=3;l++){
            count++;val=0;
            for(a1=1;a1<=5;a1++){for(a2=1;a2<=5;a2++){if(a1!=a2){
                for(a3=1;a3<=5;a3++){if(a3!=a1 && a3!=a2){
                    for(a4=1;a4<=5;a4++){if(a4!=a1 && a4!=a2 && a4!=a3){
                        val=val+y[a1,i]*y[a2,j]*y[a3,k]*y[a4,l];
                    }}
                }}
            }}}
            F[count,1]=val;
        }}}}
        ideal Iq=ideal(F),invert;
        ideal Gq=std(Iq);
        if(size(Gq)!=1 || Gq[1]!=1){ERROR("the quartic saturation is not the unit ideal");}
        "ok";
    """.splitlines())
    if zero_gram:
        end = next(i for i,line in enumerate(program) if "The row-axis classification" in line)
        return program[:end] + ['"ok";']
    return program


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    binary = shutil.which(parser.parse_args().singular)
    if not binary:
        parser.error("Singular executable missing")
    for title, source in (
        ("Generic axis", generic_program()),
        ("Zero coordinate", endpoint_program()),
        ("Zero Gram parameter, isolated diagonal", endpoint_program(zero_gram=True)),
    ):
        run = subprocess.run(
            [binary, "-q"], input="\n".join(source + ["quit;"]), text=True,
            capture_output=True, check=True,
        )
        if run.stdout.strip() != "ok" or run.stderr.strip():
            raise ArithmeticError(run.stdout[:1500] + run.stderr[:1500])
        print(f"{title} verified over its cyclotomic field.")


if __name__ == "__main__":
    main()
