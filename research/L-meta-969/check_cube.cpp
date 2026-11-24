#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

// Exhaustive separation search for the monotone edge function of the three-cube.
// Each bit stands for one ordered pair (false input, true input).
using Bits = std::array<std::uint64_t, 9>;
struct Signal {
    Bits at_false{}, at_true{}, separates{};
};
using Live = std::array<const Signal*, 16>;
constexpr std::array<std::pair<int,int>,12> edges{{
    {0,1},{0,2},{0,4},{1,3},{1,5},{2,3},{2,6},{3,7},{4,5},{4,6},{5,7},{6,7}
}};

bool target(int input) {
    for (auto [i,j] : edges)
        if ((input & (1<<i)) && (input & (1<<j))) return true;
    return false;
}

std::vector<std::pair<int,int>> tests(bool monotone) {
    std::vector<std::pair<int,int>> pairs;
    for (int input = 0; input < 256; ++input) {
        if (target(input)) continue;
        if (monotone) {
            bool maximal = true;
            for (int i = 0; i < 8; ++i)
                if (!(input & (1<<i)) && !target(input | (1<<i))) maximal = false;
            if (maximal) for (auto [i,j] : edges)
                pairs.emplace_back(input, (1<<i) | (1<<j));
        } else {
            for (int i = 0; i < 8; ++i)
                if (target(input ^ (1<<i))) pairs.emplace_back(input, input ^ (1<<i));
        }
    }
    if (monotone) assert(pairs.size() == 72);
    return pairs;
}

class Search {
    const bool monotone;
    const int block_count;
    const int limit;
    Bits domain{};
    std::array<Signal, 8> inputs;
    std::array<Signal, 16> gates;
    std::uint64_t states = 0;
    std::array<std::array<int,3>,16> path{};
    int used = 0;
    int wire_id(const Signal* node) const {
        for (int i = 0; i < 8; ++i) if (node == &inputs[i]) return i;
        for (int i = 0; i < 16; ++i) if (node == &gates[i]) return 8+i;
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
        for (const auto& input : inputs) if (same(input, signal)) return true;
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

        for (int i = 1; i < count; ++i) {
            Bits between{};
            for (int j = i-1; j >= 0; --j) {
                const Signal& a = *live[i];
                const Signal& b = *live[j];
                Bits missing{};
                for (int k = 0; k < block_count; ++k)
                    missing[k] = domain[k] & ~(prefix[j][k] | between[k] | suffix[i+1][k]);
                for (int op = 0; op < (monotone ? 2 : 4); ++op) {
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
    Search(bool mono, int bound, const std::vector<std::pair<int,int>>& pairs)
        : monotone(mono), block_count((pairs.size()+63)/64), limit(bound) {
        assert(block_count <= 9 && bound > 0 && bound <= 15);
        for (std::size_t t = 0; t < pairs.size(); ++t) {
            auto [lo,hi] = pairs[t];
            auto bit = std::uint64_t(1) << (t%64);
            domain[t/64] |= bit;
            for (int i = 0; i < 8; ++i) {
                if (lo & (1<<i)) inputs[i].at_false[t/64] |= bit;
                if (hi & (1<<i)) inputs[i].at_true[t/64] |= bit;
            }
        }
        for (auto& input : inputs) finish(input);
    }

    bool run() {
        Live live;
        for (int i=0; i<8; ++i) live[i] = &inputs[i];
        bool result = visit(live, 8, limit, 0);
        std::cout << (monotone ? "monotone" : "free-complements")
                  << " budget=" << limit << " states=" << states
                  << " result=" << (result ? "SAT" : "UNSAT") << std::endl;
        if (result && monotone) for (int k = 0; k < used; ++k)
            std::cout << 8+k << " " << (path[k][0] ? "OR" : "AND") << " "
                      << path[k][1] << " " << path[k][2] << std::endl;
        return result;
    }
};

int main(int argc, char** argv) {
    bool monotone = argc == 3 && std::string(argv[1]) == "monotone";
    if (argc != 3 || (!monotone && std::string(argv[1]) != "free-complements")) {
        std::cerr << "usage: check_cube monotone|free-complements gate_budget\n";
        return 2;
    }
    int budget = std::stoi(argv[2]);
    if (budget <= 0 || budget > 15) return 2;
    Search search(monotone, budget, tests(monotone));
    search.run();
}
