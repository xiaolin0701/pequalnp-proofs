# Exact size 39 for circuits with one layer of AND gates on F01

If no path in a monotone circuit contains two AND gates, computing the thirteen line ORs on the F01 domain requires at least 39 gates. Thirteen separate OR trees attain 39. Consequently every circuit with 37 or 38 gates, if one exists, must cascade AND gates.

Write Lₜ for the projective lines and call 0 and 1 the two distinguished points. The domain consists of the inputs for which at least one distinguished point is true or every point outside L₀ is true. The complement of every line is an allowed input. The proof uses that different lines meet in precisely one point.

## Products of original variables

First suppose all AND gates directly multiply two distinct original variables. Treat each such product as an input atom of the remaining OR circuit. Unary gates, repeated operands and constants can be simplified in advance. The expression at each output is the OR of some raw variables and some product atoms, with arbitrary sharing permitted in the OR circuit. Testing the complement of Lₜ shows that every raw variable reaching its output is on the line, and every product reaching it has at least one endpoint on the line.

For a line Lₜ containing neither 0 nor 1, attach labels to the atoms. A raw variable has its original point as label. A product of a distinguished variable and an undistinguished variable has that undistinguished point as label. All remaining products have no label. Propagate unions of labels at all OR gates. Every label reaching the output belongs to Lₜ. Conversely, for p on this line, test at {p,0}. If raw p is absent, an accepting product atom must be precisely p times 0, since the raw variable 0 cannot reach this output. Thus every line point has a label at the output. That output requires at least three OR gates carrying two or more distinct labels.

For a line Lₜ containing 0 or 1, let Uₜ be the set of raw points in its OR cone, ignoring all product labels. Its size is positive since the singleton at a distinguished point on the line forces that raw variable itself to occur. The output requires at least |Uₜ|−1 OR gates carrying two or more distinct raw points. Account for the missing points as follows.

- On a line with exactly one distinguished point α, take any missing p and test {p,β}, where β is the other distinguished point. This forces a product of p and β. A fixed such product can be charged only on the unique line through p and α.
- On the unique line L₀ containing both distinguished points, a missing point p must be undistinguished. Test at p together with every point outside L₀. Some product pq must be present with q outside L₀. The product determines its unique endpoint p on L₀. Neither endpoint is distinguished, so it cannot also be charged by the previous rule.

All missing point occurrences on the distinguished lines are therefore paid by different AND gates.

The gate counts are disjoint. Gates counted on two lines of the first family would carry two common labels. Gates counted on two lines of the second would carry two common raw points. If a gate paid by the second family also fed an output of the first, both raw points would be labels in that output, again giving two common points. In each case the projective incidence property forbids the sharing. Summing the counts gives

    number of OR gates ≥ 13·3 − number of AND gates.

For completeness, the bound of r−1 wide OR gates for r labels at a root follows by deleting empty-label nodes, contracting each node with a singleton label into that label's source, and retaining the cone of the root. There are at least r source vertices in the resulting connected binary graph. If w is the number of retained AND-free internal vertices, edge counting gives r+w−1 ≤ 2w.

## Removing ANDs with wider OR operands

In a circuit with no two ANDs on a common path, each operand of an AND is an OR of original variables after constants and copies are simplified. Any AND with an operand that ORs at least two distinct variables can be removed without increasing total size by the [wide-operand replacement](OneAndLowerBound.md). These AND gates are incomparable in the directed circuit. One may order the computation with any chosen one of them last among AND gates before doing the replacement. Every earlier AND retains its two original operands and only downstream OR gates are changed. Repeat until all surviving AND gates multiply individual original variables, and apply the count above.
