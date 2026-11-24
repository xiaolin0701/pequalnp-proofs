// Build with c++ -std=c++17 -O3 repair_circuits.cpp -o repair_circuits.
// Usage: repair_circuits near_circuits.txt max_edits first_row number_of_rows
// Rows and input indexes start at zero. Each space-separated token is a gate
// reading two earlier wires. The circuit output is wire 39, after 26 gates.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>

namespace {
using Word = std::uint64_t;
constexpr int inputs = 14, gates = 26;
constexpr std::array<int,7> neighbors{1408,8832,12544,6272,11264,5632,2816};

struct Gate { int a,b; bool disjunction; };
using Circuit = std::array<Gate,gates>;
using Wires = std::array<Word,inputs+gates>;

struct Boundary {
    Wires variables{};
    Word target = 0, domain = 0;
};

bool edge(int x) {
    for(int i=0;i<7;++i)
        if((x & (1<<i)) && (x & neighbors[i])) return true;
    return false;
}

Boundary build_boundary() {
    Boundary b;
    int rows=0;
    for(int x=0;x<(1<<inputs);++x) {
        const bool yes=edge(x);
        bool extreme=true;
        for(int i=0;i<inputs;++i) {
            if(bool(x & (1<<i))==yes && edge(x^(1<<i))==yes) extreme=false;
        }
        if(!extreme) continue;
        const Word bit=Word(1)<<rows++;
        b.domain |= bit;
        if(yes) b.target |= bit;
        for(int i=0;i<inputs;++i) if(x & (1<<i)) b.variables[i] |= bit;
    }
    if(rows!=58 || __builtin_popcountll(b.target)!=21) throw std::logic_error("incorrect frontier");
    return b;
}

Word gate_value(const Wires &w,Gate g) {
    return g.disjunction ? w[g.a] | w[g.b] : w[g.a] & w[g.b];
}

void forward(Wires &w,const Circuit &c,int start) {
    for(int i=start;i<gates;++i) w[inputs+i]=gate_value(w,c[i]);
}

Circuit parse_row(const std::string& line) {
    std::istringstream s(line);
    Circuit c;
    for(int i=0;i<gates;++i) {
        char op;
        int a,b;
        if(!(s>>a>>op>>b) || (op!='&'&&op!='|') ||
           std::min(a,b)<0 || std::max(a,b)>=inputs+i)
            throw std::runtime_error("malformed gate");
        c[i]={a,b,op=='|'};
    }
    std::string extra;
    if(s>>extra) throw std::runtime_error("extra data after last gate");
    return c;
}

void print_circuit(const Circuit &c) {
    for(auto g:c) std::printf("%d%c%d ",g.a,g.disjunction?'|':'&',g.b);
    std::putchar('\n');
}

class Search {
    const Boundary &boundary;
    Circuit circuit;
    std::uint64_t last_gate_checks=0;

    // For each input row, a mask lists which single-wire overrides change
    // the output on that row. All gates are monotone in each override, even
    // when two paths from the same source meet. If both equal operands must
    // change, take the intersection; if either suffices, take the union.
    unsigned possible_last_edits(const Wires &w,int start) const {
        unsigned available=((1u<<gates)-1) & ~((1u<<start)-1);
        for(Word wrong=w.back()^boundary.target;available && wrong;wrong &= wrong-1) {
            const Word row=wrong & -wrong;
            std::array<unsigned,inputs+gates> influence{};
            for(int j=start;j<gates;++j) {
                const auto g=circuit[j];
                const bool a=w[g.a]&row, b=w[g.b]&row;
                const unsigned u=influence[g.a],v=influence[g.b];
                unsigned inherited;
                if(a==b) {
                    const bool both_needed=g.disjunction ? a : !a;
                    inherited=both_needed ? (u & v) : (u | v);
                } else {
                    inherited=g.disjunction ? (a?u:v) : (a?v:u);
                }
                influence[inputs+j]=(1u<<j) | inherited;
            }
            available &= influence.back();
        }
        return available;
    }

    bool last_edit(const Wires &w,int start) {
        for(unsigned positions=possible_last_edits(w,start);positions;positions &= positions-1) {
            const int pos=__builtin_ctz(positions);
            Wires lo=w,hi=w;
            lo[inputs+pos]=0;
            hi[inputs+pos]=boundary.domain;
            forward(lo,circuit,pos+1);
            forward(hi,circuit,pos+1);
            ++last_gate_checks;
            if((lo.back() & ~boundary.target) || (boundary.target & ~hi.back())) continue;
            const Word yes=boundary.target & ~lo.back(), no=~boundary.target & hi.back();
            for(int a=0;a<inputs+pos;++a) {
                const bool can_and=(w[a]&yes)==yes, can_or=!(w[a]&no);
                if(!can_and && !can_or) continue;
                for(int b=a;b<inputs+pos;++b) {
                    const bool fits_and=can_and && (w[b]&yes)==yes && !(w[a]&w[b]&no);
                    const bool fits_or=can_or && !(w[b]&no) && !(yes&~(w[a]|w[b]));
                    if(fits_and || fits_or) { circuit[pos]={a,b,fits_or}; return true; }
                }
            }
        }
        return false;
    }

    bool edits(const Wires &w,int start,int remaining) {
        if(remaining==1) return last_edit(w,start);
        for(int pos=start;pos<=gates-remaining;++pos) {
            const Gate old=circuit[pos];
            // Later edits act downstream. Equal columns on the frontier are
            // interchangeable at this position. The unchanged column has
            // already been considered by the lower edit budgets.
            std::unordered_set<Word> seen{w[inputs+pos]};
            seen.reserve(1024);
            for(int a=0;a<inputs+pos;++a) for(int b=a;b<inputs+pos;++b)
                for(bool op:{false,true}) {
                    const Gate replacement{a,b,op};
                    const Word column=gate_value(w,replacement);
                    if(!seen.insert(column).second) continue;
                    Wires tmp=w;
                    tmp[inputs+pos]=column;
                    forward(tmp,circuit,pos+1);
                    circuit[pos]=replacement;
                    if(edits(tmp,pos+1,remaining-1)) return true;
                }
            circuit[pos]=old;
        }
        return false;
    }
public:
    Search(const Boundary &b,const Circuit &c) : boundary(b),circuit(c) {}

    bool run(int max_edits) {
        Wires w=boundary.variables;
        forward(w,circuit,0);
        if(__builtin_popcountll(w.back()^boundary.target)!=2)
            throw std::runtime_error("expected a two-row near solution");
        unsigned by_intervention=0;
        for(int i=0;i<gates;++i) {
            Wires changed=w;
            changed[inputs+i] ^= boundary.domain;
            forward(changed,circuit,i+1);
            const Word toggled=changed.back() ^ w.back();
            if(!((w.back() ^ boundary.target) & ~toggled)) by_intervention |= 1u<<i;
        }
        if(by_intervention!=possible_last_edits(w,0))
            throw std::logic_error("wire influence disagrees with direct interventions");
        for(int k=1;k<=max_edits;++k) if(edits(w,0,k)) {
            w=boundary.variables;
            forward(w,circuit,0);
            if(w.back()!=boundary.target) throw std::logic_error("repair verification failed");
            print_circuit(circuit);
            return true;
        }
        return false;
    }

    std::uint64_t checks() const {return last_gate_checks;}
};
} // namespace

int main(int argc,char **argv) {
    if(argc!=5) return 2;
    const int max_edits=std::stoi(argv[2]),first=std::stoi(argv[3]),limit=std::stoi(argv[4]);
    if(max_edits<1 || max_edits>gates || first<0 || limit<1) return 2;
    const auto boundary=build_boundary();
    std::ifstream file(argv[1]);
    if(!file) throw std::runtime_error("could not open candidate file");
    std::string line;
    int completed=0;
    for(int i=0;completed<limit && std::getline(file,line);++i) {
        if(i<first) continue;
        Search search(boundary,parse_row(line));
        if(search.run(max_edits)) return 0;
        std::printf("row %d has no repair within %d edits (%llu final cone checks)\n",i,max_edits,
                    (unsigned long long)search.checks());
        std::fflush(stdout);
        ++completed;
    }
    if(completed!=limit) throw std::runtime_error("requested rows extend past end of file");
}
