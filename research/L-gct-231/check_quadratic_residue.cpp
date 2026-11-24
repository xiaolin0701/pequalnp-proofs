// Exhaustive search for symmetric 4x4 permanent-level three-spaces over F_25.
// Build: c++ -std=c++17 -O3 check_quadratic_residue.cpp -o /tmp/check25
// Run /tmp/check25. Final counts: 18,610 anchors, 539 compatible pairs, zero
// triangles. Regression flags: -DPRIME_FIELD for F_5, -DFIELD_CHARACTERISTIC=3
// for F_9.
#include <algorithm>
#include <array>
#include <iostream>
#include <vector>
using namespace std;
// Default is F_25 = F_5[u]/(u^2-2). Setting PRIME_FIELD builds the F_5
// regression. F_9 uses the same quadratic polynomial and the independent
// brute-force test.
#ifndef FIELD_CHARACTERISTIC
#define FIELD_CHARACTERISTIC 5
#endif
constexpr int p = FIELD_CHARACTERISTIC;
#ifdef PRIME_FIELD
constexpr bool isPrime(int n) {
  for (int d = 2; d * d <= n; ++d)
    if (n % d == 0)
      return false;
  return n >= 2;
}
constexpr int q = p;
static_assert(p >= 5 && p < 256 && isPrime(p));
#else
static_assert(p == 3 || p == 5 || p == 7);
constexpr int q = p * p;
#endif
// Encode a+b*u by the integer a+p*b, with u^2=2 for p in {3,5} and u^2=3 for
// p=7.
using F = unsigned char;
using V = array<F, 10>;
F A[q][q], M[q][q], N[q], Inv[q], sq[q], sqrtTable[q];
int pos[4][4], w[10], g[10][10];
int add(int x, int y) { return A[x][y]; }
int mul(int x, int y) { return M[x][y]; }
int neg(int x) { return N[x]; }
int subtract(int x, int y) { return A[x][N[y]]; }
int weightedSum(const V &x) {
  int a = 0;
  for (int j = 0; j < 10; j++)
    a = add(a, mul(w[j], x[j]));
  return a;
}
int secondMatching(
    const V &x) { // twice the second matching form on the tangent hyperplane
  int a = 0, b = 0;
  for (int i = 0; i < 4; i++) {
    int s = 0;
    for (int j = 0; j < 4; j++) {
      int v = x[pos[i][j]];
      s = add(s, v);
      a = add(a, sq[v]);
    }
    b = add(b, sq[s]);
  }
  return subtract(a, mul(2, b));
}
V polarCoefficients(const V &x) {
  V res{};
  for (int j = 0; j < 10; j++) {
    int u = 0;
    for (int i = 0; i < 10; i++)
      u = add(u, mul(g[i][j], x[i]));
    res[j] = u;
  }
  return res;
}
int dot(const V &a, const V &b) {
  int u = 0;
  for (int j = 0; j < 10; j++)
    u = add(u, mul(a[j], b[j]));
  return u;
}
int permanentAt(const V &x, int t) {
  V k;
  for (int j = 0; j < 10; j++)
    k[j] = add(1, mul(x[j], t));
  // Expand along the first row and column. The lower 3x3 symmetric block
  // contributes its permanent and its six distinct permanental cofactors.
  auto [u, v, w, z, a, b, c, d, e, f] = k;
  int cof11 = add(mul(d, f), sq[e]), cof22 = add(mul(a, f), sq[c]),
      cof33 = add(mul(a, d), sq[b]);
  int cof12 = add(mul(b, f), mul(c, e)), cof13 = add(mul(b, e), mul(c, d)),
      cof23 = add(mul(a, e), mul(b, c));
  int rest = add(mul(a, cof11), add(mul(b, cof12), mul(c, cof13)));
  int diag = add(mul(sq[v], cof11), add(mul(sq[w], cof22), mul(sq[z], cof33)));
  int off = add(mul(mul(v, w), cof12),
                add(mul(mul(v, z), cof13), mul(mul(w, z), cof23)));
  return add(mul(u, rest), add(diag, mul(2, off)));
}
bool level(const V &x) { // caller ensures tangent and secondMatching=0, only
                         // degrees 3 and 4 remain
  return permanentAt(x, 1) == 24 % p && permanentAt(x, 2) == 24 % p;
}
// The restrictions of the cubic and quartic to a pencil already vanish on both
// coordinate axes. Three further nonzero slopes force all mixed coefficients to
// vanish.
bool compatiblePair(const V &a, const V &b) {
  for (int t : {1, 2, 3}) {
    V c{};
    for (int j = 0; j < 10; j++)
      c[j] = add(a[j], mul(t, b[j]));
    if (!level(c))
      return false;
  }
  return true;
}
// When all pairs are compatible, interpolate once more in the slope between
// the first two directions to test the whole three-space.
bool triple(const V &a, const V &b, const V &c) {
  for (int t : {1, 2, 3}) {
    V v{};
    for (int j = 0; j < 10; j++)
      v[j] = add(a[j], mul(t, b[j]));
    if (!compatiblePair(v, c))
      return false;
  }
  return true;
}
int pivot(const V &v) {
  return find_if(v.begin(), v.end(), [](F x) { return x != 0; }) - v.begin();
}
V normal(V v) {
  int f = Inv[v[pivot(v)]];
  for (auto &x : v)
    x = mul(x, f);
  return v;
}
// pool[i][j] is the list of projective level directions vanishing on
// coordinates i,j.
vector<V> pool[10][10];
bool done[10][10];
// Enumerate all level directions with two specified coordinates zero. Of the
// eight remaining coordinates, the first six are projectively normalized in
// fill(). The tangent equation expresses the last coordinate in terms of the
// penultimate coordinate. The second matching equation is then one quadratic in
// that coordinate.
struct Cut {
  vector<int> ind;
  int j, k;
  vector<V> lines;
  V x{}, L{}, gradient{};
  int quadratic;
  void test(int b, int z) {
    int yk = subtract(z, mul(mul(w[j], Inv[w[k]]), b));
    x[j] = b;
    x[k] = yk;
    if (level(x))
      lines.push_back(x);
    x[j] = x[k] = 0;
  }
  void solve() {
    int z = mul(neg(weightedSum(x)), Inv[w[k]]);
    x[k] = z;
    // Solve secondMatching(x + t L)=quadratic*t^2+linear*t+constant, with the
    // last offset chosen by tangency.
    int constant = secondMatching(x), linear = dot(gradient, x);
    x[k] = 0;
    if (quadratic == 0) {
      if (linear)
        test(mul(neg(constant), Inv[linear]), z);
      else if (constant == 0)
        for (int t = 0; t < q; t++)
          test(t, z);
      return;
    }
    int disc = subtract(sq[linear], mul(4 % p, mul(quadratic, constant))),
        h = sqrtTable[disc];
    if (h == q)
      return;
    int den = Inv[mul(2, quadratic)];
    test(mul(subtract(h, linear), den), z);
    if (h)
      test(mul(subtract(neg(h), linear), den), z);
  }
  void fill(int h, bool lead) {
    if (h == 6) {
      if (lead)
        solve();
      return;
    }
    int k = ind[h];
    if (!lead) {
      x[k] = 0;
      fill(h + 1, false);
      x[k] = 1;
      fill(h + 1, true);
    } else
      for (int s = 0; s < q; s++) {
        x[k] = s;
        fill(h + 1, true);
      }
    x[k] = 0;
  }
  explicit Cut(int s, int t) {
    for (int n = 0; n < 10; n++)
      if (n != s && n != t)
        ind.push_back(n);
    j = ind[6];
    k = ind[7];
    L[j] = 1;
    L[k] = neg(mul(w[j], Inv[w[k]]));
    quadratic = secondMatching(L);
    gradient = polarCoefficients(L);
    if (quadratic == 0 && level(L))
      lines.push_back(L);
    fill(0, false);
  }
};
int main() {
  for (int i = 0; i < q; i++)
    for (int j = 0; j < q; j++) {
      int a = i % p, b = i / p, c = j % p, d = j / p;
      A[i][j] = (a + c) % p + p * ((b + d) % p);
      M[i][j] =
          (a * c + (p == 7 ? 3 : 2) * b * d) % p + p * ((a * d + b * c) % p);
    }
  fill_n(sqrtTable, q, q);
  for (int i = 0; i < q; i++) {
    N[i] = M[p - 1][i];
    sq[i] = M[i][i];
    sqrtTable[sq[i]] = i;
    for (int j = 0; j < q; j++)
      if (M[i][j] == 1)
        Inv[i] = j;
  }
  int next = 0;
  for (int i = 0; i < 4; i++)
    for (int j = i; j < 4; j++) {
      pos[i][j] = pos[j][i] = next;
      w[next++] = i == j ? 1 : 2;
    }
  for (int i = 0; i < 10; i++)
    for (int j = 0; j < 10; j++) {
      V a{}, b{}, c{};
      a[i] = b[j] = 1;
      c = a;
      c[j] = add(c[j], 1);
      g[i][j] = subtract(subtract(secondMatching(c), secondMatching(a)),
                         secondMatching(b));
    }
  // Simultaneous permutation of the four matrix indices preserves the permanent
  // and the matchings. The 45 pairs of positions form five orbits.
  for (int a = 0; a < 10; a++)
    for (int b = a + 1; b < 10; b++)
      if (!done[a][b]) {
        Cut cut(a, b);
        cerr << "cut " << a << " " << b << " size " << cut.lines.size() << endl;
        array<int, 4> p{0, 1, 2, 3};
        do {
          array<int, 10> to;
          for (int i = 0; i < 4; i++)
            for (int j = i; j < 4; j++)
              to[pos[i][j]] = pos[p[i]][p[j]];
          int l = min(to[a], to[b]), s = max(to[a], to[b]);
          if (done[l][s])
            continue;
          done[l][s] = true;
          for (auto x : cut.lines) {
            V y;
            for (int j = 0; j < 10; j++)
              y[to[j]] = x[j];
            pool[l][s].push_back(normal(y));
          }
        } while (next_permutation(p.begin(), p.end()));
      }
  // Every three-space contains nonzero a with a[0]=a[1]=0. With pivot k of a,
  // choose b with b[0]=b[k]=0. With pivot l of b, choose c with c[k]=c[l]=0.
  // Their pivot coordinates prove independence. A successful three-space must
  // therefore occur in these loops, possibly through several distinct bases.
  long long pairs = 0, triangles = 0, planes = 0;
  long long anchors = 0;
  for (auto const &a : pool[0][1]) {
    int k = pivot(a);
    auto ga = polarCoefficients(a);
    for (auto const &b : pool[0][k]) {
      if (dot(ga, b) || !compatiblePair(a, b))
        continue;
      pairs++;
      int l = pivot(b);
      auto gb = polarCoefficients(b);
      for (auto const &c : pool[min(k, l)][max(k, l)]) {
        if (dot(ga, c) || dot(gb, c) || !compatiblePair(a, c) ||
            !compatiblePair(b, c))
          continue;
        triangles++;
        bool passes = triple(a, b, c);
        if constexpr (q == 49) {
          // For the two candidates in F_49, cross-check by enumerating every
          // linear combination until a failing translated permanent is found.
          bool exhaustive = true;
          for (int i = 0; i < q && exhaustive; ++i) {
            for (int j = 0; j < q && exhaustive; ++j) {
              for (int k = 0; k < q; ++k) {
                V test{};
                for (int n = 0; n < 10; ++n)
                  test[n] = add(mul(i, a[n]), add(mul(j, b[n]), mul(k, c[n])));
                if (permanentAt(test, 1) != 24 % p) {
                  exhaustive = false;
                  break;
                }
              }
            }
          }
          if (passes != exhaustive)
            return 1;
        }
        if (passes) {
          planes++;
          if (planes == 1)
            for (auto *v : {&a, &b, &c}) {
              for (F x : *v)
                cerr << (int)x << " ";
              cerr << endl;
            }
        }
      }
    }
    if (++anchors % 5000 == 0)
      cerr << "anchors " << anchors << " pairs " << pairs << " full " << planes
           << endl;
  }
  cout << "anchors " << anchors << " pairs " << pairs
       << " independent triangles " << triangles << " full " << planes << endl;
}
