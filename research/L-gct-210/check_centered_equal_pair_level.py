"""Exact unit-ideal test for a nine-plane with a centered nonisotropic common normal.

Run with Python 3 and Singular 4.  Use --singular /path/to/Singular if needed.
The default six-variable chart follows the repeated-coordinate theorem in
CenteredPairNormalParameters.md. --unrestricted keeps all eight independent
coordinates, and --emit writes the generated Singular program for inspection.
"""

import argparse
import itertools
from pathlib import Path
import shutil
import subprocess


def singular_program(unrestricted):
    if unrestricted:
        variables = "a,b,c,d,l,m,n,o"
        w = ["a", "d", "b", "c", "1-a-d-b-c"]
        h = ["l", "o", "m", "n", "60-l-o-m-n"]
    else:
        variables = "a,b,c,l,m,n"
        w = ["a", "a", "b", "c", "1-2*a-b-c"]
        h = ["l", "l", "m", "n", "60-2*l-m-n"]
    lines = [f"ring R=0,({variables}),dp;"]
    indices = range(1, 6)
    for i, (weight, bottom) in enumerate(zip(w, h), 1):
        lines.extend((f"poly w{i}={weight};", f"poly h{i}={bottom};",
                      f"poly f{i}=-3*h{i}+150*w{i}-12;",
                      f"poly k{i}=(h{i}-75*w{i}+3)/4;"))

    def coordinate_sum(pattern):
        return "+".join(pattern.format(i=i) for i in indices)

    lines.append("poly delta=" + coordinate_sum("w{i}^3") + "-1;")
    polys = [coordinate_sum("w{i}^2") + "-1",
             coordinate_sum("w{i}*h{i}") + "-76",
             coordinate_sum("k{i}^2") + "+75/4",
             coordinate_sum("k{i}*(w{i}^2-w{i}-delta*k{i})")]
    for t in range(1, 6):
        level, opposite = [], []
        for i, j in itertools.combinations(indices, 2):
            bottom = "*".join(f"(1+{t}*h{k})" for k in indices if k not in (i, j))
            level.append(f"(1+{t}*f{i})*(1+{t}*f{j})*{bottom}")
            opposite.append(f"w{i}*w{j}*{bottom}")
        polys.append("+".join(level) + "-10")
        if t <= 3:
            polys.append("+".join(opposite))
    lines.extend(("ideal I=" + ",\n".join(polys) + ";", "option(redSB);",
                  "ideal C=slimgb(I);", 'if(size(C)==1 && C[1]==1){"UNIT_IDEAL_OVER_Q";}',
                  "quit;"))
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--singular", default="Singular")
    parser.add_argument("--unrestricted", action="store_true")
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    program = singular_program(args.unrestricted)
    if args.emit:
        args.emit.write_text(program)
    executable = shutil.which(args.singular)
    if not executable:
        parser.error("Singular executable not found; pass --singular /path/to/Singular")
    result = subprocess.run([executable, "-q"], input=program, text=True,
                            capture_output=True, check=True)
    if result.stdout.strip() != "UNIT_IDEAL_OVER_Q":
        raise RuntimeError("Unexpected Singular result: " + result.stdout + result.stderr)
    count = 8 if args.unrestricted else 6
    print(f"The {count}-variable rational ideal has reduced Gröbner basis [1].")


if __name__ == "__main__":
    main()
