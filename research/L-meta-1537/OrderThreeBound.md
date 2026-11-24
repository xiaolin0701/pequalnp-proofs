# The order-three counting inequality

For a wire w define S(w) as the set of points whose singleton input makes w
true. An input wire has a one-point support. A missing read contributes the
empty set. The singleton supports of OR and AND gates are the union and
intersection of their operand supports, including the full plane for a
nullary AND. Correctness on arcs includes every singleton, so the designated
output of a line l has support exactly l. Every line has four points.

Write b=|B|. Every line in B has no escape in the sense of the formal row.
Each h in H has at least two singleton points, all contained in a line *with*
an escape. Two points determine at most one line. Consequently each gate
having at least two singleton points all contained in a line of B lies
outside H. A gate whose support strictly contains a whole line is also
outside H, since its support contains at least five points.

For each l in B select the first gate with singleton support equal to l.
These b gates are distinct and outside H. If it is an OR, neither operand
already equals l, and the four points cannot be covered by two singleton
operands. Thus one earlier operand is a gate with a wide proper subset of
l. One such helper chosen for each OR line gives t distinct gates outside H
in addition to the b first gates, because no pair of points lies in two
lines. If the first gate is an AND, its two operand supports are distinct
strict supersets of l and their intersection is l. Empty-input and unary
gates cannot first produce a four-point line.

Count by m the distinct gates that serve as a strict-superline operand of
such a first AND. These gates are all outside H and distinct from the b+t
already counted. The same unordered pair of operand gates cannot produce
two different line supports. Consequently, with g the number of gates,

    g−|H| ≥ b+t+m,     b ≤ t + m(m−1)/2.

For 1≤b≤12 one has t+m≥ceil(b/2). To check the small integer implication,
fix s=t+m. The convex quadratic t+binom(m,2) is maximized at m=0 or m=s.
For s=0,1,2,3,4,5 its upper bounds are 0,1,2,3,6,10 respectively.
If s<ceil(b/2), then b≥2s+1 and s≤5, contradicting these bounds. The case
b=0 is automatic from H being a set of gate indices.

For b=13 all lines have no escape, so H is empty. If g≤19, then t+m≤6.
For t≥1 this gives t+binom(m,2)≤11, too small. Thus t=0 and m=6, and
all 19 gates consist of 13 first lines and six strict-superline operands.
The first gate cannot have four-point support or support strictly between
four points and thirteen: it can only read input bits or missing wires.
The sole candidate among these nineteen gate types is the full-plane
constant from a nullary AND. Intersecting it with any strict superline
operand reproduces the latter (and therefore does not produce a line).
It cannot serve in the six counted operands. This contradiction finishes
the last case.

Therefore the inequality 3|B|+2|H|≤2g holds for **every** order-three
incidence system satisfying the formal axioms. The leakage condition is
used only to separate the two families of lines. No classification of
order-three planes is needed. This is an order-three result; the Lean
statement quantifies over all natural orders q.

The program submitted for the assigned triangle range is search.py.
On PG(2,3) it enumerates all 234 triangular line triples and checks the
necessary support transitions for every possible ordered operand pair.
Its SHA-256 is abcfa3718e05bfa8a9a992646dbf7310bbf1858a9dd6d854b709ccd7adba0fa4.
