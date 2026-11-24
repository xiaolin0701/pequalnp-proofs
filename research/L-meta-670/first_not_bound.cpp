#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

// Three exhaustive live-signal searches for the shard whose first gate is NOT x4.
// Each bit stands for one ordered pair (false input, true input).
using Bits = std::array<std::uint64_t, 4>;
struct Signal {
    Bits at_false{}, at_true{}, separates{};
};
using Live = std::array<const Signal*, 16>;
using Pair = std::pair<int,int>;
struct Graph {
    const char* name;
    int vertices;
    std::vector<Pair> edges;
    std::vector<int> marked;
    int budget;
    bool monotone;

    bool target(int mask) const {
        for (auto [i,j] : edges)
            if ((mask & (1 << i)) && (mask & (1 << j))) return true;
        return false;
    }
};

const Graph theta{"theta",7,{{0,2},{2,1},{0,3},{3,4},{4,1},{0,5},{5,6},{6,1}}, {},10,false};
const Graph core{"core",8,{{0,1},{1,2},{2,3},{0,4},{1,5},{2,6},{3,7},{4,6},{5,7},{7,4}},
                 {0,3,5,6},12,false};
const Graph full{"full",9,{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{5,7},{6,8},{8,5}},
                 {4,6,7},14,true};

std::vector<Pair> tests(const Graph& graph) {
    std::vector<Pair> pairs;
    for (int input = 0; input < (1 << graph.vertices); ++input) {
        if (graph.target(input)) continue;
        if (graph.monotone) {
            bool maximal = true;
            for (int i=0; i<graph.vertices; ++i)
                if (!(input & (1<<i)) && !graph.target(input | (1<<i))) maximal = false;
            if (maximal) for (auto [i,j] : graph.edges)
                pairs.emplace_back(input,(1<<i) | (1<<j));
        } else {
            for (int i=0; i<graph.vertices; ++i)
                if (graph.target(input ^ (1<<i))) pairs.emplace_back(input,input ^ (1<<i));
        }
    }
    return pairs;
}

// A rename is verified on every full assignment, not merely on the sampled boundaries.
void verify_deletions(const Graph& graph, const Graph& smaller) {
    const int n=smaller.vertices;
    if (graph.vertices!=n+1) throw std::logic_error("unexpected deletion size");
    for (int marked : graph.marked) {
        std::vector<int> permutation(n);
        std::iota(permutation.begin(),permutation.end(),0);
        bool found=false;
        do {
            bool same=true;
            for (int mask=0; mask<(1<<n) && same; ++mask) {
                int full_mask=0, pos=0;
                for (int i=0; i<graph.vertices; ++i) if (i!=marked) {
                    if (mask & (1<<permutation[pos])) full_mask |= 1<<i;
                    ++pos;
                }
                same=(graph.target(full_mask)==smaller.target(mask));
            }
            if (same) { found=true; break; }
        } while (std::next_permutation(permutation.begin(),permutation.end()));
        if (!found) throw std::logic_error("nonisomorphic deletion");
    }
}

class Search {
    const Graph& graph;
    const bool monotone;
    std::array<bool,25> marked{};
    const int block_count;
    const int limit;
    int first_zero_row;
    Bits domain{};
    std::array<Signal, 9> inputs;
    std::array<Signal, 16> gates;
    std::uint64_t states = 0;
    std::array<std::array<int,3>,16> path{};
    int used = 0;
    int wire_id(const Signal* node) const {
        for (int i=0; i<graph.vertices; ++i) if (node==&inputs[i]) return i;
        for (int i = 0; i < 16; ++i) if (node == &gates[i]) return graph.vertices+i;
        std::abort();
    }

    void finish(Signal& signal) const {
        // Every wire may be complemented for free in the relaxed circuit model.
        bool invert = !monotone && (signal.at_false[0] & 1);
        for (int k = 0; k < block_count; ++k) {
            if (invert) {
                signal.at_false[k] ^= domain[k];
                signal.at_true[k] ^= domain[k];
            }
            signal.separates[k] = monotone
                ? signal.at_true[k] & ~signal.at_false[k]
                : signal.at_true[k] ^ signal.at_false[k];
        }
    }

    static std::uint64_t operation(int op, std::uint64_t a, std::uint64_t b) {
        switch (op) {
        case 0: return a & b;
        case 1: return a | b;
        case 2: return a & ~b;
        default: return ~a & b;
        }
    }

    static bool same(const Signal& a, const Signal& b) {
        return a.at_false == b.at_false && a.at_true == b.at_true;
    }

    bool previously_available(const Signal& signal, int depth) const {
        for (int i=0; i<graph.vertices; ++i) if (same(inputs[i],signal)) return true;
        for (int g = 0; g < depth; ++g) if (same(gates[g], signal)) return true;
        return false;
    }

    bool visit(const Live& live, int count, int remaining, int depth) {
        ++states;
        if (!remaining || count > remaining + 1) return false;

        // Forward/backward unions allow us to remove a chosen pair in O(block_count).
        std::array<Bits, 17> prefix{}, suffix{};
        for (int i = 0; i < count; ++i) for (int k = 0; k < block_count; ++k)
            prefix[i+1][k] = prefix[i][k] | live[i]->separates[k];
        for (int i = count-1; i >= 0; --i) for (int k = 0; k < block_count; ++k)
            suffix[i][k] = suffix[i+1][k] | live[i]->separates[k];

        // At this bound no current signal can branch in a successful remaining tree.
        if (!graph.marked.empty() && count == remaining + 1) {
            for (int i = 0; i < count; ++i) {
                bool positive = false, negative = false;
                for (int k = 0; k < block_count; ++k) {
                    auto exclusive = domain[k] & ~(prefix[i][k] | suffix[i+1][k]);
                    positive |= bool(exclusive & live[i]->at_true[k] & ~live[i]->at_false[k]);
                    negative |= bool(exclusive & live[i]->at_false[k] & ~live[i]->at_true[k]);
                }
                if (positive && negative) return false;
            }
        }
        for (int i = 1; i < count; ++i) {
            Bits between{};
            for (int j = i-1; j >= 0; --j) {
                const Signal& a = *live[i];
                const Signal& b = *live[j];
                const int ai=wire_id(&a), bi=wire_id(&b);
                const bool am=marked[ai], bm=marked[bi];
                Bits missing{};
                for (int k = 0; k < block_count; ++k)
                    missing[k] = domain[k] & ~(prefix[j][k] | between[k] | suffix[i+1][k]);
                for (int op = 0; op < (monotone ? 2 : 4); ++op) {
                    // Fixing a marked input to zero may save only one binary gate.
                    // A constant output here would also simplify its next consumer.
                    const std::uint64_t az = (first_zero_row >> ai) & 1, bz = (first_zero_row >> bi) & 1;
                    if (am && ((operation(op,az,0) ^ operation(op,az,1)) & 1) == 0) continue;
                    if (bm && ((operation(op,0,bz) ^ operation(op,1,bz)) & 1) == 0) continue;
                    Signal& out = gates[depth];
                    for (int k = 0; k < block_count; ++k) {
                        out.at_false[k] = operation(op, a.at_false[k], b.at_false[k]);
                        out.at_true[k] = operation(op, a.at_true[k], b.at_true[k]);
                    }
                    finish(out);
                    path[depth] = {op,wire_id(&a),wire_id(&b)};
                    if (out.at_false == Bits{} && out.at_true == domain) {
                        used = depth+1;
                        return true;
                    }
                    if ((out.at_false == Bits{} && out.at_true == Bits{}) ||
                        (out.at_false == domain && out.at_true == domain) ||
                        previously_available(out, depth)) continue;
                    for (int keep = 0; keep < 4; ++keep) {
                        bool keep_a = keep & 1, keep_b = keep & 2;
                        // A marked input cannot have two direct consumers.
                        if ((keep_a && am) || (keep_b && bm)) continue;
                        int next_count = count - 1 + keep_a + keep_b;
                        if (next_count > remaining) continue;
                        bool feasible = true;
                        for (int k = 0; k < block_count; ++k) {
                            auto uncovered = missing[k] & ~out.separates[k];
                            if (keep_a) uncovered &= ~a.separates[k];
                            if (keep_b) uncovered &= ~b.separates[k];
                            if (uncovered) { feasible = false; break; }
                        }
                        if (!feasible) continue;
                        Live next;
                        int n = 0;
                        for (int t = 0; t < count; ++t)
                            if ((t != i || keep_a) && (t != j || keep_b))
                                next[n++] = live[t];
                        next[n++] = &out;
                        if (visit(next, n, remaining-1, depth+1)) return true;
                    }
                }
                for (int k = 0; k < block_count; ++k) between[k] |= b.separates[k];
            }
        }
        return false;
    }

public:
    Search(const Graph& g, const std::vector<Pair>& pairs)
        : graph(g), monotone(g.monotone), block_count((pairs.size()+63)/64), limit(g.budget) {
        if (pairs.empty() || block_count>4 || limit>15) throw std::logic_error("profile exceeds array bounds");
        first_zero_row = monotone ? 0 : pairs.front().first;
        for (int i : graph.marked) marked[i]=true;
        for (std::size_t t = 0; t < pairs.size(); ++t) {
            auto [lo,hi] = pairs[t];
            auto bit = std::uint64_t(1) << (t%64);
            domain[t/64] |= bit;
            for (int i=0; i<graph.vertices; ++i) {
                if (lo & (1<<i)) inputs[i].at_false[t/64] |= bit;
                if (hi & (1<<i)) inputs[i].at_true[t/64] |= bit;
            }
        }
        for (int i=0; i<graph.vertices; ++i) finish(inputs[i]);
    }

    bool run() {
        Live live;
        for (int i=0; i<graph.vertices; ++i) live[i] = &inputs[i];
        bool result = visit(live, graph.vertices, limit, 0);
        std::cout << graph.name << " " << (monotone ? "monotone" : "free-complements")
                  << " budget=" << limit << " states=" << states
                  << " result=" << (result ? "SAT" : "UNSAT") << std::endl;
        if (result) for (int k = 0; k < used; ++k)
            std::cout << graph.vertices+k << " " << path[k][0] << " "
                      << path[k][1] << " " << path[k][2] << std::endl;
        return result;
    }
};

int main(int argc, char** argv) {
    std::string which = argc==1 ? "all" : argv[1];
    if (argc>2 || (which!="all" && which!="theta" && which!="core" && which!="full")) {
        std::cerr << "usage: first_not_bound [all|theta|core|full]\n";
        return 2;
    }
    verify_deletions(core,theta);
    verify_deletions(full,core);
    for (const Graph* graph : {&theta,&core,&full}) {
        if (which!="all" && which!=graph->name) continue;
        auto pairs=tests(*graph);
        std::cout << graph->name << " pairs=" << pairs.size() << std::endl;
        Search search(*graph,pairs);
        if (search.run()) return 1;
    }
    return 0;
}
