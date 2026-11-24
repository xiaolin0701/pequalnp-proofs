// Search all rational 3-planes on the symmetric 4-by-4 level over F_p.
// Build: c++ -std=c++17 -O3 check_residue_planes.cpp -o check_residue_planes
// Optional compile-time prime: -DRESIDUE_PRIME=7 (we tested 5, 7 and 13).
#include <algorithm>
#include <array>
#include <iostream>
#include <vector>

#ifndef RESIDUE_PRIME
#define RESIDUE_PRIME 13
#endif
constexpr int prime = RESIDUE_PRIME;
static_assert(prime == 5 || prime == 7 || prime == 13);
using Point = std::array<int, 10>;
using PermutationCells = std::array<int, 4>;

struct Search {
    std::array<int, 10> weight{};
    std::array<int, prime> inverse{};
    std::vector<PermutationCells> permutations;
    std::vector<Point> points;

    Search() {
        int cell[4][4]{};
        int next = 0;
        for (int i = 0; i < 4; ++i) {
            for (int j = i; j < 4; ++j) {
                cell[i][j] = cell[j][i] = next;
                weight[next++] = i == j ? 1 : 2;
            }
        }
        std::array<int, 4> permutation{0, 1, 2, 3};
        do {
            PermutationCells cells;
            for (int i = 0; i < 4; ++i) cells[i] = cell[i][permutation[i]];
            permutations.push_back(cells);
        } while (std::next_permutation(permutation.begin(), permutation.end()));
        for (int a = 1; a < prime; ++a)
            for (int b = 1; b < prime; ++b)
                if (a * b % prime == 1) inverse[a] = b;
    }

    static int residue(int n) {
        int result = n % prime;
        return result < 0 ? result + prime : result;
    }

    int level_value(const Point& point, int t) const {
        Point entries{};
        for (int j = 0; j < 10; ++j) entries[j] = residue(1 + t * point[j]);
        int sum = 0;
        for (const auto& cell : permutations)
            sum += entries[cell[0]] * entries[cell[1]] * entries[cell[2]] * entries[cell[3]];
        return sum % prime;
    }

    // Constant term is 24 and the weighted sum guarantees zero linear term.
    // The remaining polynomial divided by t^2 has degree at most two.
    bool level_direction(const Point& point) const {
        for (int t : {1, -1, 2})
            if (level_value(point, t) != 24 % prime) return false;
        return true;
    }

    void fill_support(Point& point, const std::vector<int>& support, int i, int sum) {
        int j = support[i];
        if (i + 1 == static_cast<int>(support.size())) {
            point[j] = residue(-sum * inverse[weight[j]]);
            if (point[j] && level_direction(point)) points.push_back(point);
            return;
        }
        for (int value = 1; value < prime; ++value) {
            point[j] = value;
            fill_support(point, support, i + 1, sum + weight[j] * value);
        }
    }

    void collect_points() {
        for (int mask = 1; mask < (1 << 10); ++mask) {
            std::vector<int> support;
            for (int i = 0; i < 10; ++i)
                if ((mask >> i) & 1) support.push_back(i);
            if (support.size() < 2 || support.size() > 8) continue;
            Point point{};
            int first = support.front();
            point[first] = 1;
            fill_support(point, support, 1, weight[first]);
        }
    }

    static Point add_multiple(const Point& a, const Point& b, int t) {
        Point result{};
        for (int i = 0; i < 10; ++i) result[i] = (a[i] + t * b[i]) % prime;
        return result;
    }

    bool level_pair(const Point& a, const Point& b) const {
        // Each homogeneous level form has degree at most four. Its restriction
        // to a pencil already vanishes at the two axes; three slopes suffice.
        for (int t = 1; t <= 3; ++t)
            if (!level_direction(add_multiple(a, b, t))) return false;
        return true;
    }

    bool level_triple(const Point& a, const Point& b, const Point& c) const {
        // The two bounding planes with c have already passed. With the other
        // coordinates fixed, again interpolate in the projective slope of a,b.
        for (int t = 1; t <= 3; ++t)
            if (!level_pair(add_multiple(a, b, t), c)) return false;
        return true;
    }

    static int pivot(const Point& point) {
        return std::find_if(point.begin(), point.end(), [](int x){ return x != 0; }) - point.begin();
    }

    void count_planes() const {
        std::vector<int> zero[10][10];
        for (int i = 0; i < static_cast<int>(points.size()); ++i)
            for (int j = 0; j < 10; ++j)
                for (int k = 0; k < 10; ++k)
                    if (j != k && !points[i][j] && !points[i][k]) zero[j][k].push_back(i);

        // Any 3-space meets the cut x0=x1=0 in a nonzero a with pivot k>=2.
        // In the same space take b with xk=x0=0 and pivot l!=k, then c with
        // xk=xl=0. These three nonzero vectors are automatically independent.
        long long pairs = 0, triangles = 0, plane_bases = 0;
        for (int ia : zero[0][1]) {
            const Point& a = points[ia];
            int k = pivot(a);
            for (int ib : zero[k][0]) {
                const Point& b = points[ib];
                if (!level_pair(a, b)) continue;
                ++pairs;
                for (int ic : zero[k][pivot(b)]) {
                    const Point& c = points[ic];
                    if (!level_pair(a, c) || !level_pair(b, c)) continue;
                    ++triangles;
                    if (level_triple(a, b, c)) ++plane_bases;
                }
            }
        }
        std::cout << "prime " << prime << ", projective points with support <= 8 "
                  << points.size() << ", anchors " << zero[0][1].size()
                  << ", compatible anchor pairs " << pairs << ", triangles " << triangles
                  << ", plane bases " << plane_bases << '\n';
    }
};

int main() {
    Search search;
    search.collect_points();
    search.count_planes();
}
