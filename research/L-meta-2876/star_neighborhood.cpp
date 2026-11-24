#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <set>
#include <utility>

using Word = std::uint64_t;
constexpr int n = 14, star_size = 27;
constexpr std::array<int,7> neighbors{1408,8832,12544,6272,11264,5632,2816};
struct Gate { int left, right; bool is_or; };
using Circuit = std::array<Gate,star_size>;
using Wires = std::array<Word,n+star_size>;
Word expected;
int positives = 0, negatives = 0;

bool edge(int mask) {
    for (int v=0; v<7; ++v)
        if ((mask & (1<<v)) && (mask & neighbors[v])) return true;
    return false;
}

Wires frontier() {
    Wires inputs{};
    int row = 0;
    for (int mask=0; mask<(1<<n); ++mask) {
        const bool label=edge(mask);
        bool extreme=true;
        for (int j=0;j<n;++j)
            if (bool(mask & (1<<j)) == label && edge(mask^(1<<j)) == label)
                extreme=false;
        if (!extreme) continue;
        if (label) { expected |= Word(1)<<row; ++positives; }
        else ++negatives;
        for (int i=0;i<n;++i)
            if (mask & (1<<i)) inputs[i] |= Word(1)<<row;
        ++row;
    }
    return inputs;
}

Circuit stars(bool balanced) {
    Circuit gates{};
    int size=0;
    auto gate = [&](int a,int b,bool is_or) {
        gates[size] = {a,b,is_or};
        return n+size++;
    };
    std::array<int,7> terms{};
    for (int v=0;v<7;++v) {
        std::array<int,3> terms_v{};
        int count=0;
        for (int i=7;i<n;++i)
            if (neighbors[v] & (1<<i)) terms_v[count++]=i;
        const int pair=gate(terms_v[0],terms_v[1],true);
        terms[v]=gate(v,gate(pair,terms_v[2],true),false);
    }
    if (balanced) {
        const int a=gate(terms[0],terms[1],true);
        const int b=gate(terms[2],terms[3],true);
        const int c=gate(terms[4],terms[5],true);
        const int d=gate(a,b,true);
        const int e=gate(c,terms[6],true);
        gate(d,e,true);
    } else {
        int sum=terms[0];
        for (int v=1;v<7;++v) sum=gate(sum,terms[v],true);
    }
    return gates;
}

Word get(const Gate& g,const Wires& w) {
    return g.is_or ? (w[g.left]|w[g.right]) : (w[g.left]&w[g.right]);
}

void one_edit(const Circuit& gates,const Wires& inputs) {
    Wires check=inputs;
    for (int i=0;i<star_size;++i) check[n+i]=get(gates[i],check);
    if(check.back()!=expected) std::abort();
    std::uint64_t edits=0, full=0;
    int best=positives+negatives;
    for (int drop=0;drop<star_size;++drop) {
        for (int proxy=0;proxy<n+drop;++proxy) {
            // Keeping a slot as a pure alias is equivalent to deleting it and
            // redirecting its later reads. Replacements may read the alias.
            Wires wires=inputs;
            for (int i=0;i<star_size;++i)
                wires[n+i]=i==drop?wires[proxy]:get(gates[i],wires);
            for (int change=0;change<star_size;++change) {
                if(change==drop) continue;
                // With this input prefix fixed, equal truth columns give
                // identical downstream evaluations for every possible edit.
                std::set<Word> alternatives;
                for(int a=0;a<n+change;++a) for(int b=a;b<n+change;++b) {
                    alternatives.insert(wires[a]&wires[b]);
                    alternatives.insert(wires[a]|wires[b]);
                    edits+=2;
                }
                for(Word column:alternatives) {
                    Wires tmp=wires;
                    tmp[n+change]=column;
                    for (int j=change+1;j<star_size;++j)
                        tmp[n+j]=j==drop?tmp[proxy]:get(gates[j],tmp);
                    const int errors=__builtin_popcountll(tmp.back()^expected);
                    best=std::min(best,errors);
                    if(errors==0) ++full;
                }
            }
        }
    }
    std::printf("%llu raw trials; minimum frontier errors %d; exact replacements %llu\n",
                (unsigned long long)edits,best,(unsigned long long)full);
}

void two_edits(const Circuit& gates,const Wires& inputs) {
    unsigned long long trials=0,pairs=0;
    for (int drop=0;drop<star_size;++drop) {
        for (int proxy=0;proxy<n+drop;++proxy) {
            Wires baseline=inputs;
            for (int i=0;i<star_size;++i)
                baseline[n+i]=i==drop?baseline[proxy]:get(gates[i],baseline);
            for (int first=0;first<star_size-1;++first) {
                if(first==drop) continue;
                std::set<Word> alternatives;
                for(int a=0;a<n+first;++a) for(int b=a;b<n+first;++b) {
                    alternatives.insert(baseline[a]&baseline[b]);
                    alternatives.insert(baseline[a]|baseline[b]);
                }
                // All later wires depend on this replacement only through its 58-row column.
                for(Word col:alternatives) {
                    Wires w=baseline;w[n+first]=col;
                    for(int i=first+1;i<star_size;++i)
                        w[n+i]=i==drop?w[proxy]:get(gates[i],w);
                    for(int second=first+1;second<star_size;++second) {
                        if(second==drop) continue;
                        ++trials;
                        Wires lo=w,hi=w;
                        lo[n+second]=0;hi[n+second]=(1ull<<(positives+negatives))-1;
                        for(int j=second+1;j<star_size;++j){
                            const auto& g=gates[j];
                            lo[n+j]=j==drop?lo[proxy]:get(g,lo);
                            hi[n+j]=j==drop?hi[proxy]:get(g,hi);
                        }
                        // The output is monotone in the edited wire. Its two endpoint columns
                        // determine exactly which rows require a 0 or 1 at that wire.
                        if((lo.back()&~expected)||(expected&~hi.back())) continue;
                        Word yes=expected&~lo.back(),no=~expected&hi.back();
                        for(int a=0;a<n+second;++a) {
                            bool and_possible=(w[a]&yes)==yes,or_possible=(w[a]&no)==0;
                            if(!and_possible&&!or_possible)continue;
                            for(int b=a;b<n+second;++b) {
                                ++pairs;
                                bool can_and=and_possible&&(w[b]&yes)==yes&&!(w[a]&w[b]&no);
                                bool can_or=or_possible&&!(w[b]&no)&&(yes&~(w[a]|w[b]))==0;
                                if(can_or||can_and) {
                                    printf("solution: drop %d alias %d, change %d to column %llx, change %d to %d %s %d\n",
                                        drop,proxy,first,(unsigned long long)col,second,a,can_or?"OR":"AND",b);
                                    exit(0);
                                }
                            }
                        }
                    }
                }
            }
        }
        fprintf(stderr,"drop %d done, %llu staged columns\n",drop,trials);
    }
    printf("%llu staged column/second-gate pairs, %llu concrete last checks: no solution\n",trials,pairs);
}
int main(){
    const Wires inputs=frontier();
    std::printf("frontier %d positive + %d negative\n", positives, negatives);
    for(bool balanced : {false,true}) {
        std::printf("%s reduction tree\n", balanced ? "balanced" : "left-associated");
        const Circuit gates = stars(balanced);
        one_edit(gates, inputs);
        two_edits(gates, inputs);
    }
}
