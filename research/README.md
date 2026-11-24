# P vs NP contributions from ylwang0701

This branch collects proof sources, checked special cases, mathematical notes, and finite search programs from the November 2026 contributions. Each directory uses the problem ID assigned by the project. The upstream pull request and its checker comment record the status of a submission. A local theorem or finite search can also document progress on an open problem.

## Submitted work

The final submission was [upstream PR #7000](https://github.com/open-goat/pequalnp-proofs/pull/7000), a three-part reduction of L-meta-1904. Complete proofs of the first two parts are in [SolvedChildren.lean](L-meta-1904/SolvedChildren.lean). They cover forests, individual cycles of length at least five, and the circuit construction from a minimum vertex cover. The matching lower bound on the remaining graphs is open.

The upstream checker accepted the complete proofs [#5512](https://github.com/open-goat/pequalnp-proofs/pull/5512) and [#5607](https://github.com/open-goat/pequalnp-proofs/pull/5607), and the reductions [#5185](https://github.com/open-goat/pequalnp-proofs/pull/5185) and [#6381](https://github.com/open-goat/pequalnp-proofs/pull/6381). All submissions are listed in the [upstream PR history for ylwang0701](https://github.com/open-goat/pequalnp-proofs/pulls?q=is%3Apr+author%3Aylwang0701).

## Selected proofs and calculations

- **L-meta-3364.** The minimum monotone formula size for the positive and negative samples, counted in leaves, is exactly N(q+2). For general circuits the gate lower bound is 3N, which proves the full rectangle-cover conclusion through order 299. The higher-order case with unrestricted sharing remains open. [Minimum formula size](L-meta-3364/OptimalFormula.lean) · [Gate bound](L-meta-3364/Plane299.lean)
- **L-meta-2082 and L-meta-3136.** The formula equality case constrains occurrences of endpoint inputs. Separate circuit results classify short prefixes of the Petersen graph computation. The directories include Lean proofs and bounded computational checks. [Formula equality case](L-meta-2082/EdgeReadOnce.lean) · [Prefix classification](L-meta-3136/EarlyParent.lean)
- **L-gct-210.** The five-by-five permanent problem asks for an upper bound of eight. The materials include a formal seven-dimensional construction, a written general upper bound of ten, and a bound of eight under a common left and right null-vector hypothesis. [Construction](L-gct-210/ComplexFamily.lean) · [Upper bound of ten](L-gct-210/RescaledTenBound.md) · [Common null vectors](L-gct-210/BoundsForArbitraryCommonNormals.md)
- **L-gct-231.** The symmetric four-by-four problem asks for a three-dimensional space over the complex numbers. The two-dimensional hook space is maximal among the spaces containing it. Every nonzero valid direction has matrix rank at least two. Separate finite-field calculations are documented with their assumptions and commands. [Hook space](L-gct-231/HookMaximal.lean) · [Rank obstruction](L-gct-231/RankOneObstruction.lean) · [Finite-field checks](L-gct-231/PermutationSymmetry.md)

## Reproducing the Lean checks

Use the toolchain in the repository's `lean/lean-toolchain`. With the project's Lake dependencies installed, run these commands from the repository root.

```sh
cd lean
../research/L-meta-1904/check.sh
../research/L-meta-3364/check.sh
../research/L-meta-2082/check.sh
```

These scripts print the axioms used by the corresponding Lean results. The 1904 check builds its supporting upstream modules. The scientific notes distinguish formal proofs, calculations in a specified finite field, and arguments on paper.
