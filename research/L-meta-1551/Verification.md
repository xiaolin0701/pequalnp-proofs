# Minimum circuit size for the theta graph with path lengths 3, 4 and 4

The edge function on ten Boolean variables has minimum circuit size 15 in the project's fan-in-two AND/OR/NOT model. The lower bound below is an exhaustive C++ computation. The desk assigned L-meta-1551, which asks for a counterexample of size at most 14. The positive lower bound is L-meta-1549.

## Upper bound

Use five terms. They are $x_0(x_2+x_4+x_7)$, $x_1(x_3+x_6+x_9)$, $x_2x_3$, $x_5(x_4+x_6)$, and $x_8(x_7+x_9)$, where addition means OR and multiplication means AND. These use respectively 3, 3, 1, 2 and 2 gates. Combining their outputs costs four more. The checker independently evaluates this expression on all 1,024 assignments.

## Two searches for the lower bound

A putative circuit of size at most 14 either has no NOT gate, or has at most 13 binary AND/OR gates. The first search uses a monotone circuit of budget 14. In the second search every wire, including each primary input and the output, can be complemented freely, with a budget of 13 binary gates. This relaxation includes every circuit in the latter case.

Implement the official default-false semantics by wiring a constant false wherever a gate reads a missing input or a forward wire. Fold constants, ignore the second input of NOT, bypass unary aliases, and cut away gates outside the output cone. A gate with two occurrences of the same signal, allowing free complementation in the relaxed model, is an alias or constant. The target function depends on all ten inputs and is nonconstant. These reductions never increase the binary-gate cost.

Each test consists of an input where the target is zero followed by an input where it is one. A wire signature gives its values at both ends of every test.

* For the monotone search, use all 15 maximal independent sets as negative inputs and all 11 graph edges as positive inputs. A test needs a live wire whose values are zero and one in that order. If a live state has no such wire, the positive endpoint is at most the negative endpoint coordinatewise, so a monotone continuation cannot produce the target values. Every variable is essential on these tests. For an edge $\{i,j\}$, choose a maximal independent set containing $j$. The only primary wire that separates that ordered pair in the necessary direction is $i$.
* For the free-complement search use all 522 pairs where the two graph inputs differ in one variable and the target changes from zero to one. Every test needs two distinct values on some live wire. Every variable is essential already on the pair consisting of a neighbor alone and that neighbor together with the variable. Store both polarities as one signature, choosing the orientation with first negative bit zero. Up to output complement the four operations $a\wedge b$, $a\vee b$, $a\wedge\neg b$, and $\neg a\wedge b$ include all signed uses of an AND or OR.

Among all circuits matching the test outputs, take a minimum-binary-gate circuit. The cases in the preceding paragraph imply that all ten inputs enter the output cone. A constant internal signature could be propagated away; an internal signature that previously occurred could be replaced by that earlier signal on every later use. Thus the minimum has neither. In the relaxed model, take equality up to free complementation. These simplifications apply to the sampled function because all later gate values on the chosen tests depend only on those signatures.

Traverse the gates of this minimum circuit in topological order. At each stage the live signals are exactly those used again. Enumerate each unordered pair of distinct live signals, each allowed operation and each of the four possibilities for keeping the operands after the gate. Fresh outputs are live. With $d$ live signals and $k$ remaining gates, $d\le k+1$ is necessary since each binary gate can reduce the number of live components by at most one. Equivalently, a connected output cone with $d$ sources and at most $k$ binary vertices has at most $2k$ edges and at least $d+k-1$ edges when all $k$ vertices are used. At each stage discard any state failing a test's necessary separation condition. Every minimum correct circuit follows one of the remaining branches. The reference implementation enumerates all first pairs and uses no gate-order, graph-automorphism, or hashing shortcut.

## Reproduction

```sh
c++ -O3 -std=c++17 -Wall -Wextra -pedantic check_theta.cpp -o /tmp/check_theta
/tmp/check_theta monotone 14
/tmp/check_theta free-complements 13
```

The two runs use fixed-size bit vectors to evaluate all tests exactly. They terminate with UNSAT. The source also verifies the 15-gate construction on the full truth table by a direct assertion.

The monotone run visited 14,138,459 states. The free-complement run visited 4,530,891 states. The SHA-256 digest of the source is `fdbf56388a9efe6fab22b756347f4846f4e20167c73974280a4c8659d06769ff`.

The formal 15-gate upper bound in FifteenGateUpper.lean compiled with the project's Lean toolchain using the command below from its lean directory. It uses the exact HasCircuitSize definition and edge ordering.

```sh
lake env lean ../../L-meta-1551/FifteenGateUpper.lean
```
