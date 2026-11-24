# The three-cube edge function has monotone circuit size 13

The vertices are the three-bit strings, numbered 0 through 7. The output accepts precisely when the chosen vertices contain two strings at Hamming distance one. The 13 gates in `ThirteenGateUpper.lean` use two prior wires each. Wires 8 and 9 compute `x₂ ∨ x₁` and `x₇ ∨ x₄`. Four more OR gates supply the four neighbor lists of vertices 3, 0, 6 and 5. Each of four AND gates attaches the corresponding vertex, and three OR gates combine those four stars. This also checks every edge directly, since the four centers form one bipartition class of the cube.

## Reproducing the finite lower bound

In the directory containing this file run

```sh
c++ -O3 -std=c++17 check_cube.cpp -o /tmp/check_cube
/tmp/check_cube monotone 11
/tmp/check_cube monotone 12
/tmp/check_cube monotone 13
```

The three runs visit 127,973, 7,462,421 and 37,259,195 search states, respectively. The first two exhaust their budgets. The last prints the explicit circuit above.

The search tracks a signal on the twelve edge inputs and six maximal independent sets. Monotonicity implies that these extremal inputs determine whether the signal computes the target. Each of their 72 ordered pairs must be separated in the direction zero at its independent set and one at its edge. At every cut through a valid computation at least one live wire separates each pair. Otherwise the negative side dominates the positive side coordinatewise on every live wire, and all later monotone gates preserve that relation.

A state consists of the live wires, every previously computed test signature and the remaining gate budget. Each new gate chooses two distinct live wires and computes their AND or OR. Each operand may separately be retained or retired. In a minimal circuit, gates outside the output cone can be omitted. All eight inputs are essential. Reading every wire through its last use is therefore among the explored schedules. A state with more than one additional live wire per remaining gate cannot end with just the output, since one binary gate decreases the number of live wires by at most one. A state losing separation on any pair also cannot finish.

A constant intermediate signal on all tests can be propagated through AND and OR on the tests. Repeated test signatures can be replaced everywhere by the earlier wire, and repeated operands or unary gates are copies. These substitutions keep all extremal test values and decrease the gate count. Nullary gates are constants. The official evaluator returns false for an out-of-bounds wire at the moment of evaluation, so these reads can also be simplified as constants. Thus every smaller circuit in the stated model would give a circuit covered by the finite search.

The project’s existing Lean result L-meta-970 independently excludes eleven gates. The stronger exclusion of twelve gates above uses the accompanying C++ enumeration. The Lean file verifies the upper bound against the circuit evaluator.
