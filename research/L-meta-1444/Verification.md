# L-meta-1444, ten five-input truth tables

The posted statement is the negation of the positive row L-meta-1443. The
independent program checks the positive row. The ten monotone upper-bound
circuits come from [PR 3083](https://github.com/brilliant-hq/pequalnp-proofs/pull/3083).
The program evaluates every circuit on all 32 inputs and performs its own
lower-bound search directly on the full truth tables.

For an upper circuit of m gates, a shorter circuit containing a NOT uses at
most m−2 binary gates. Give every wire a free complement. The binary choices
on two wires are then AND, OR, AND-NOT, and its reverse, up to complement.
All constant, unary, invalid-read, repeated or semantically duplicate wires
can be bypassed in this enlarged model. If a proposed shorter circuit has
no NOT, it already qualifies as its own replacement.

The search enumerates subsets of the five inputs used by a candidate. A
state contains just wires that a retained suffix still reads. For a new
binary gate it tries every pair, every operation, and all four choices of
which of the two predecessor wires to keep alive. A gate whose result is
constant or duplicates an existing live wire can be omitted. This covers
every legal circuit after removing gates that do not lead to the output
and bypassing redundant operations. If a state with h live wires can reach
one output in k binary gates, h≤k+1: each gate reduces the live count by
at most one. A successful state must also distinguish every positive from
every negative input assignment, since gate operations cannot separate
assignments on which all currently live wires agree.

All ten upper circuits evaluate correctly, and every lower search at m−2
returned UNSAT. The hardest case visited 139,123 recursion states. Thus the
positive comparison holds for all ten functions, and the leased negation is
false. Build and run with:

```sh
clang++ -std=c++17 -O3 L-meta-1444/search.cpp -o /tmp/one-output-5
/tmp/one-output-5
```

The negative row is labelled “shard 15” in its title. Its actual desk response
contained an ordinary theorem and had no top-level shard range or shard
specification.
