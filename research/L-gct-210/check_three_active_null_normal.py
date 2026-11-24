"""Unit-ideal test for the three-active centered residual of a normalized normal.

The check uses exact arithmetic over Q. The default residual product is 1;
other rational inputs can be checked by passing --product p/q.
"""

import argparse
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import shutil
import subprocess


def lower_terms(degree, i, radial):
    terms = []
    for z in range(3):
        k = z + degree - 3
        if k == 2:
            continue
        power = 3 - z
        for exponent_l in range(power + 1):
            j = i - exponent_l
            if not (0 <= j <= k):
                continue
            weight = (1 if degree == 3 else -3 if degree == 4
                      else -4 + Fraction(25*j*(k-j), k*(k-1)))
            weight *= Fraction((-1)**power * comb(3, z)*comb(power, exponent_l),
                               comb(5, k))
            terms.append(f"({weight})*({radial[0]})^{exponent_l}*({radial[1]})^{power-exponent_l}*e{k}_{j}")
    return "(0+" + "+".join(terms) + ")"


def pivot_weights(degree, i):
    base = 1-degree + Fraction(5*i*(degree-i), 4)
    factor = Fraction(1, 10) if degree == 3 else -Fraction(3, 5) if degree == 4 else base
    return base, factor


def recurrence(program, product, variables, equations, radial):
    for degree, values in ((0, [1]), (1, [1, 1]), (2, [0, 0, 0])):
        for i, value in enumerate(values):
            program.append(f"poly e{degree}_{i}={value};")

    for degree in (3, 4, 5):
        for i in range(degree + 1):
            base, factor = pivot_weights(degree, i)
            pivot = base + product*factor
            residual = lower_terms(degree, i, radial)
            if pivot:
                program.append(f"poly e{degree}_{i}=({-product/pivot})*{residual};")
            else:
                equations.append(residual)
                name = f"g{degree}_{i}"
                if product == -1:  # The six quintic compatibility equations suffice.
                    name = "0"
                else:
                    variables.append(name)
                program.append(f"poly e{degree}_{i}={name};")


def jets_at(program, index, x, y, axis):
    """Specialize the quintic and its first two transverse derivatives."""
    terms = [[], [], []]
    for degree in range(6):
        for i in range(degree + 1):
            for order in range(3):
                a = i-order if axis == "x" else i
                b = degree-i if axis == "x" else degree-i-order
                if min(a,b) < 0:
                    continue
                power = a if axis == "x" else b
                factor = (x**a * y**b * factorial(power+order)) // factorial(power)
                if factor:
                    terms[order].append(f"({factor})*e{degree}_{i}*s^{5-degree}")
    p, first, second = [f"p{index}_{i}" for i in range(3)]
    for name, data in zip((p, first, second), terms):
        program.append(f"poly {name}=" + "+".join(data) + ";")
    program.extend((f"poly num{index}={second}*diff({p},s)^2"
                    f"-2*diff({first},s)*diff({p},s)*{first}+diff(diff({p},s),s)*{first}^2;",
                    f"poly rem{index}=reduce(num{index},std(ideal({p})));",
                    f"int j{index}; for(j{index}=0;j{index}<5;j{index}++)"
                    f"{{I=I,subst(rem{index},s,0);rem{index}=diff(rem{index},s);}}"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--product", type=Fraction, default=Fraction(1))
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    if not args.product:
        parser.error("The three active residual coordinates have nonzero product.")
    fixed = {Fraction(20): Fraction(3, 5), Fraction(-5): Fraction(4, 15)}
    if args.product in fixed:
        nonzero = fixed[args.product]
        cases = [(str(nonzero), "0"), (str(nonzero), str(nonzero))]
    else:
        cases = [("l", "m")]
    executable = shutil.which(args.singular)
    if not executable:
        parser.error("Singular executable not found; pass --singular /path/to/Singular")
    for case_index, radial in enumerate(cases):
        program = []
        variables = ["k", "l", "m"] if radial == ("l", "m") else ["k"]
        equations = ["k*l-1"] if radial == ("l", "m") else ["k"]
        recurrence(program, args.product, variables, equations, radial)
        names = ",".join(variables)
        program.insert(0, f"ring R=0,(s,{names}),(lp(1),dp({len(variables)}));")
        program.append("ideal I=" + ",".join(equations) + ";")
        if args.product != -1:
            points = ((1, 0, "y"), (0, 1, "x"), (1, 1, "y"), (1, -1, "y"))
            if len(variables) > 3 or len(cases) > 1:
                points += ((1, 2, "y"), (1, -2, "y"))
            for i, (x, y, axis) in enumerate(points):
                jets_at(program, i, x, y, axis)
        program.extend((f"ring A=0,({names}),dp;", "ideal IA=imap(R,I);", "option(redSB);",
                        "ideal G=slimgb(IA);", 'if(size(G)==1 && G[1]==1){"UNIT_IDEAL_OVER_Q";}',
                        "quit;"))
        source = "\n".join(program) + "\n"
        if args.emit:
            target = args.emit if len(cases) == 1 else args.emit.with_suffix(f".{case_index}.sing")
            target.write_text(source)
        result = subprocess.run([executable, "-q"], input=source, text=True,
                                capture_output=True, check=True)
        if result.stdout.strip() != "UNIT_IDEAL_OVER_Q":
            raise RuntimeError("Unexpected Singular output: " + result.stdout + result.stderr)
    print(f"All rational curvature or compatibility ideals for product {args.product} have basis [1].")


if __name__ == "__main__":
    main()
