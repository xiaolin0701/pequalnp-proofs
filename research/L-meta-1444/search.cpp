// Exact fan-in-two synthesis on all 32 assignments, with complemented wires free.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <vector>

using Word = uint32_t;
using Cuts = std::array<uint64_t, 4>;
using Wires = std::vector<Word>;

Word normalize(Word w) { return (w & 1u) ? ~w : w; }

struct Solver {
    Word target;
    Cuts required{};
    std::vector<std::pair<unsigned, unsigned>> pairs;
    std::unordered_map<Word, Cuts> cached;
    uint64_t calls = 0;

    explicit Solver(Word t) : target(normalize(t)) {
        for (unsigned a = 0; a < 32; a++)
            for (unsigned b = 0; b < 32; b++)
                if ((target >> a & 1) && !(target >> b & 1)) {
                    unsigned k = static_cast<unsigned>(pairs.size());
                    required[k / 64] |= uint64_t(1) << (k % 64);
                    pairs.emplace_back(a, b);
                }
    }

    const Cuts& cuts(Word w) {
        auto item = cached.emplace(w, Cuts{});
        if (item.second) {
            Cuts& result = item.first->second;
            for (unsigned i = 0; i < pairs.size(); i++) {
                auto [a, b] = pairs[i];
                if (((w >> a) ^ (w >> b)) & 1)
                    result[i / 64] |= uint64_t(1) << (i % 64);
            }
        }
        return item.first->second;
    }

    bool separates(const Wires& w) {
        Cuts all{};
        for (Word x : w) {
            const Cuts& c = cuts(x);
            for (unsigned i = 0; i < 4; i++) all[i] |= c[i];
        }
        return all == required;
    }

    bool search(const Wires& w, unsigned left) {
        ++calls;
        if (std::find(w.begin(), w.end(), target) != w.end()) return true;
        if (!left || w.size() > left + 1 || !separates(w)) return false;
        for (unsigned i = 0; i < w.size(); i++) {
            for (unsigned j = i + 1; j < w.size(); j++) {
                const Word a = w[i], b = w[j];
                Wires rest;
                for (unsigned k = 0; k < w.size(); k++)
                    if (k != i && k != j) rest.push_back(w[k]);
                for (Word raw : {a & b, a | b, a & ~b, ~a & b}) {
                    const Word z = normalize(raw);
                    if (!z || std::find(w.begin(), w.end(), z) != w.end()) continue;
                    for (unsigned keep = 0; keep < 4; keep++) {
                        unsigned count = rest.size() + 1 + (keep & 1) + (keep >> 1);
                        if (count > left) continue;
                        Wires next = rest;
                        next.push_back(z);
                        if (keep & 1) next.push_back(a);
                        if (keep & 2) next.push_back(b);
                        if (search(next, left - 1)) return true;
                    }
                }
            }
        }
        return false;
    }

    bool run(unsigned budget) {
        const Word input[5] = {0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000};
        for (unsigned mask = 0; mask < 32; mask++) {
            Wires start;
            for (unsigned j = 0; j < 5; j++) if (mask >> j & 1) start.push_back(input[j]);
            if (search(start, budget)) return true;
        }
        return false;
    }
};

struct Gate { bool is_or; unsigned a, b; };

bool check_upper(Word target, const std::vector<Gate>& gates) {
    Wires wires = {0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000};
    for (const Gate& g : gates) {
        if (g.a >= wires.size() || g.b >= wires.size()) return false;
        Word a = wires[g.a], b = wires[g.b];
        wires.push_back(g.is_or ? a | b : a & b);
    }
    return wires.back() == target;
}

int main() {
    // Monotone witnesses from k-sandhu, public PR 3083 (commit 59f6ba8).
    // Their evaluation and the fully enumerated lower bounds here are independent.
    const std::pair<Word, std::vector<Gate>> rows[] = {
        {0xfeeafcc0, {{true, 1, 3}, {false, 2, 5}, {false, 0, 4}, {false, 1, 3}, {true, 6, 8}, {true, 7, 9}}},
        {0xeeeaeaea, {{false, 3, 4}, {true, 2, 5}, {false, 1, 6}, {true, 0, 7}}},
        {0xeeeaeee8, {{true, 2, 3}, {true, 4, 5}, {false, 0, 6}, {true, 0, 5}, {true, 1, 7}, {false, 8, 9}}},
        {0xeeeeeee0, {{true, 2, 3}, {true, 0, 1}, {true, 4, 5}, {false, 6, 7}}},
        {0xfee8eee8, {{false, 3, 4}, {true, 0, 1}, {true, 5, 6}, {false, 0, 1}, {false, 2, 7}, {true, 8, 9}, {false, 3, 6}, {true, 10, 11}}},
        {0xfeeaeaaa, {{false, 1, 3}, {false, 1, 4}, {false, 2, 3}, {false, 2, 4}, {true, 6, 7}, {true, 5, 8}, {false, 9, 10}, {true, 0, 11}}},
        {0xfeeaeae8, {{true, 1, 2}, {true, 3, 5}, {false, 4, 5}, {false, 1, 2}, {true, 0, 8}, {true, 4, 6}, {false, 3, 7}, {true, 9, 11}, {false, 10, 12}}},
        {0xfeeaece8, {{true, 0, 1}, {false, 2, 5}, {true, 1, 4}, {true, 0, 3}, {true, 2, 5}, {false, 7, 8}, {false, 9, 10}, {true, 6, 11}}},
        {0xfeeaeee0, {{true, 2, 3}, {true, 0, 1}, {false, 2, 3}, {true, 0, 7}, {false, 4, 8}, {false, 5, 6}, {true, 9, 10}}},
        {0xfeeafcc8, {{true, 2, 3}, {false, 2, 3}, {true, 1, 6}, {false, 5, 7}, {true, 1, 4}, {false, 0, 9}, {true, 8, 10}}},
    };
    for (const auto& [table, gates] : rows) {
        if (!check_upper(table, gates)) return EXIT_FAILURE;
        const unsigned monotone = gates.size();
        Solver s(table);
        bool found = s.run(monotone - 2);
        std::printf("%08x budget %u %s after %llu states\n", table, monotone - 2,
                    found ? "SAT" : "UNSAT", (unsigned long long)s.calls);
        std::fflush(stdout);
        if (found) return EXIT_FAILURE;
    }
}
