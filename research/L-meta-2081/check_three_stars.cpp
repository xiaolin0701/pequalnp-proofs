#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Sep = unsigned __int128;
using Edge = std::pair<int, int>;

struct Signal {
    Word value;
    Sep separates;
};

class Checker {
    std::vector<Edge> edges;
    std::vector<unsigned> tests;
    int vertices, budget, positive, negative;
    std::array<int,2> base, derivative;
    Word goal, observations;
    Sep all_pairs;
    std::array<Signal,26> wires{};
    std::uint64_t visits=0;

    bool edgeFunction(unsigned mask) const {
        for (auto [a,b] : edges) if ((mask>>a & 1) && (mask>>b & 1)) return true;
        return false;
    }
    Signal make(Word value) const {
        Sep sep=0;
        for(int j=0;j<positive;++j) if(value>>j&1) {
            const Word failures=(~(value>>positive)) & ((Word(1)<<negative)-1);
            sep |= Sep(failures) << (negative*j);
        }
        return {value,sep};
    }
    static bool bit(Word w,int i) {return (w>>i)&1;}
    bool isGoal(Word w) const {
        return (w & observations)==goal && !bit(w,derivative[0]) && !bit(w,derivative[1]);
    }
    bool visit(std::array<int,26> live,int n,int depth) {
        ++visits;
        const int left=budget-depth;
        if(!left || n>left+1) return false;
        for(int i=0;i<n;++i) for(int j=0;j<=i;++j) {
            const auto a=wires[live[i]], b=wires[live[j]];
            Sep other=0;
            for(int k=0;k<n;++k) if(k!=i && k!=j) other|=wires[live[k]].separates;
            for(int isOr=0;isOr<2;++isOr) {
                if(i==j && isOr) continue;
                Word w;
                if(isOr) w=a.value|b.value;
                else {
                    w=(a.value & b.value) & ((Word(1)<<derivative[0])-1);
                    for(int k=0;k<2;++k) if(
                        (bit(a.value,base[k]) && bit(b.value,derivative[k])) ||
                        (bit(b.value,base[k]) && bit(a.value,derivative[k])))
                        w |= Word(1)<<derivative[k];
                }
                if(isGoal(w)) return true;
                bool seen=false;
                for(int k=0;k<vertices+depth;++k) if(wires[k].value==w) {seen=true;break;}
                if(seen || !w) continue;
                const int id=vertices+depth;
                wires[id]=make(w);
                for(int keep=0;keep<(i==j?2:4);++keep) {
                    const auto rem=left-1;
                    const bool ki=keep&1, kj=keep&2;
                    int newn=n-(i==j?1:2)+1+int(ki)+int(kj);
                    if(newn>rem+1 || !rem) continue;
                    Sep sep=other|wires[id].separates|(ki?a.separates:0)|(kj?b.separates:0);
                    if(sep!=all_pairs) continue;
                    std::array<int,26> next{};
                    int m=0;
                    for(int k=0;k<n;++k)
                        if((k!=i && k!=j) || (k==i && ki) || (k==j && kj)) next[m++]=live[k];
                    next[m++]=id;
                    assert(m==newn);
                    if(visit(next,m,depth+1)) return true;
                }
            }
        }
        return false;
    }
public:
    Checker(int n,int bound,std::vector<Edge> graph,Edge target) : edges(std::move(graph)),vertices(n),budget(bound) {
        for(auto [u,v]:edges) tests.push_back((1u<<u)|(1u<<v));
        positive=int(tests.size());
        for(unsigned x=0;x<(1u<<vertices);++x) {
            if(edgeFunction(x)) continue;
            bool maximal=true;
            for(int i=0;i<vertices;++i) if(!(x>>i&1) && !edgeFunction(x|1u<<i)) maximal=false;
            if(maximal) tests.push_back(x);
        }
        negative=int(tests.size())-positive;
        observations=(Word(1)<<tests.size())-1;
        goal=(Word(1)<<positive)-1;
        if (positive*negative > 128 || tests.size()+4>64 || vertices+budget>26) throw std::runtime_error("profile too large");
        all_pairs=positive*negative==128 ? ~Sep(0) : (Sep(1)<<(positive*negative))-1;
        const auto [u,v]=target;
        base={int(tests.size()),int(tests.size())+1};
        tests.push_back(1u<<v);
        tests.push_back(1u<<u);
        derivative={int(tests.size()),int(tests.size())+1};
        for(int i=0;i<vertices;++i) {
            Word w=0;
            for(int j=0;j<int(tests.size());++j) if(tests[j]>>i&1) w |= Word(1)<<j;
            if(i==u) w|=Word(1)<<derivative[0];
            if(i==v) w|=Word(1)<<derivative[1];
            wires[i]=make(w);
        }
    }
    bool run() {
        std::array<int,26> live{};
        for(int i=0;i<vertices;++i) live[i]=i;
        auto result=visit(live,vertices,0);
        std::cout << "vertices=" << vertices << " budget=" << budget << " states=" << visits
                  << " result=" << (result ? "SAT" : "UNSAT") << '\n';
        return result;
    }
};
int main(int argc, char** argv) {
    std::cout << std::unitbuf;
    if(argc>1) {
        std::vector<Edge> theta;
        for(int i=0;i<3;++i) {theta.emplace_back(0,i+2);theta.emplace_back(i+2,i+5);theta.emplace_back(i+5,1);}
        const std::string mode=argv[1];
        if(mode=="end") return Checker(8,12,theta,{0,2}).run();
        if(mode=="middle") return Checker(8,12,theta,{2,5}).run();
        if(mode=="end-leaf" || mode=="middle-leaf"){int u=mode=="end-leaf"?1:2;theta.emplace_back(u,8);return Checker(9,13,theta,{u,8}).run();}
        return 2;
    }
    bool sat=false;
    std::vector<Edge> cycle;
    for(int i=0;i<6;++i) cycle.emplace_back(i,(i+1)%6);
    sat |= Checker(6,8,cycle,{0,1}).run();
    cycle.emplace_back(0,6);
    sat |= Checker(7,9,cycle,{0,6}).run();
    for(int k : {3,4}) {
        std::vector<Edge> star;
        for(int i=0;i<k;++i) {
            star.emplace_back(0,i+1);
            star.emplace_back(i+1,i+1+k);
        }
        for(auto target : {star[0],star[1]}) {
            std::cout << "collinear " << k << " target=" << target.first << "," << target.second << " ";
            sat |= Checker(2*k+1,3*k-1,star,target).run();
        }
    }
    return sat;
}
