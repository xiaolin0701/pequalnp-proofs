# The Petersen distance-two deletion has circuit size twelve

The lower bound in the posted L-meta-1664 reduces to the accepted eleven-gate lower bound for the theta graph with three paths of lengths two, three and three (L-meta-517). The leaf is vertex 6. Setting it to false removes its edge with vertex 2. The variable is essential, as witnessed by the input with only vertex 2 true, and the restricted function is nonconstant. Constant propagation in a fan-in-two circuit therefore removes at least one gate. The reindexing from the original graph into the theta numbering is [3,0,2,1,4,5,7,6], with coordinate 7 used for the restricted leaf. The proof in L_meta_1664.lean includes both checked auxiliary arguments.

TwelveGateUpper.lean proves that an explicit monotone twelve-gate circuit computes the same edge function. Its truth values were also compared on all 256 assignments. Since the lower proof permits AND, OR and NOT, the full-basis optimum is twelve.

The C++ search provides an independent finite check. Compile and run from this directory.

```sh
c++ -std=c++17 -O3 check.cpp -o /tmp/petersen-dist-two
/tmp/petersen-dist-two monotone 11
/tmp/petersen-dist-two free-complements 10
/tmp/petersen-dist-two monotone 12
```

The calls respectively exhaust 221,890 monotone states, exhaust 41,160 states with free wire complementation, and find a twelve-gate circuit after 1,104,618 states. Any circuit with eleven gates that uses a NOT has at most ten binary gates, so the second search also covers that case. The monotone search uses all 81 pairs of minimal positive and maximal negative inputs. The free-complement search uses adjacent false and true assignments. An unseparated pair at a cut cannot be recovered by a later gate. The search tries both binary operands and all four choices of which operand wires have a later use. The associated completeness argument for the shared enumerator is developed in [the cube verification](../L-meta-969/CubeSearch.md).
