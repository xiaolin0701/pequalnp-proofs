#include <algorithm>
#include <array>
#include <cstring>
#include <string>
#include <cstdlib>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Word = std::uint64_t;
#include <bitset>
using Sep = std::bitset<256>;
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
    std::array<Signal,32> wires{};
    std::uint64_t visits=0,hits=0;
    struct Slot { std::array<std::uint32_t, 18> sig; };
    std::vector<Slot> cache=std::vector<Slot>(1<<21);
    int banmask=0;
    // A hash collision only replaces an entry. Pruning checks the entire sorted signature list.
    bool memo(const std::array<int,32>& live,int n,int depth) {
        if(n>16) return false;
        std::array<std::uint32_t,18> sig={}; sig[0]=depth+1;sig[1]=n;
        for(int i=0;i<n;++i) sig[i+2]=std::uint32_t(wires[live[i]].value) | ((live[i]<vertices && banmask) ? (1u<<31) : 0);
        std::sort(sig.begin()+2,sig.begin()+2+n);
        Word hash=0x243f6a8885a308d3ULL;
        for(int i=0;i<n+2;++i) hash=(hash^(sig[i]+0x9e3779b9))*0x100000001b3ULL;
        hash^=hash>>32;
        auto &slot=cache[hash&(cache.size()-1)];
        if(slot.sig==sig) { ++hits; return true; }
        slot.sig=sig;
        return false;
    }

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
    bool visit(std::array<int,32> live,int n,int depth) {
        ++visits;
        const int left=budget-depth;
        if(memo(live,n,depth)) return false;
        if(visits%25000000==0) std::cerr<<"visits "<<visits<<" hits "<<hits<<std::endl;
        if(!left || n>left+1) return false;
        for(int i=0;i<n;++i) for(int j=0;j<=i;++j) {
            const auto a=wires[live[i]], b=wires[live[j]];
            bool mi=live[i]<vertices && ((banmask >> live[i]) & 1);
            bool mj=live[j]<vertices && ((banmask >> live[j]) & 1);
            // A marked input has one OR consumer with an internal second operand.
            if((mi && live[j]<vertices) || (mj && live[i]<vertices)) continue;
            Sep other=0;
            for(int k=0;k<n;++k) if(k!=i && k!=j) other|=wires[live[k]].separates;
            for(int isOr=0;isOr<2;++isOr) {
                if(i==j && isOr) continue;
                if(!isOr && (mi||mj))continue;
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
                for(int k=0;k<n;++k) if(wires[live[k]].value==w) {seen=true;break;}
                if(seen || !w) continue;
                const int id=vertices+depth;
                wires[id]=make(w);
                for(int keep=0;keep<(i==j?2:4);++keep) {
                    const auto rem=left-1;
                    const bool ki=keep&1, kj=keep&2;
                    if((mi && ki) || (mj && kj))continue;
                    int newn=n-(i==j?1:2)+1+int(ki)+int(kj);
                    if(newn>rem+1 || !rem) continue;
                    Sep sep=other|wires[id].separates|(ki?a.separates:Sep(0))|(kj?b.separates:Sep(0));
                    if(sep!=all_pairs) continue;
                    std::array<int,32> next{};
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
        if (positive*negative > 256 || tests.size()+4>31 || vertices+budget>32) throw std::runtime_error("profile too large");
        all_pairs=(~Sep(0))>>(256-positive*negative);
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
    bool run(int marks=0) {
        banmask=marks;
        std::array<int,32> live{};
        for(int i=0;i<vertices;++i) live[i]=i;
        auto result=visit(live,vertices,0);
        std::cout << "vertices=" << vertices << " budget=" << budget << " states=" << visits
                  << " result=" << (result ? "SAT" : "UNSAT") << '\n';
        return result;
    }
};

int main(int argc,char**argv) {
 std::cout<<std::unitbuf;
 if(argc<2)return 2;
 std::string mode=argv[1];
 std::vector<Edge> edges;
 if(mode.starts_with("theta")){
   // 0-2-1, 0-3-4-5-1, 0-6-7-8-1.
   edges={{0,2},{1,2},{0,3},{3,4},{4,5},{5,1},{0,6},{6,7},{7,8},{8,1}};
   if(mode=="thetaLeaf0" || mode=="thetaLeaf4"){
        int u=mode=="thetaLeaf0"?0:4; edges.emplace_back(u,9); return Checker(10,14,edges,{u,9}).run();
   }
   int idx=atoi(mode.c_str()+5);
   return Checker(9,13,edges,edges.at(idx)).run();
 }
 if(mode=="regress"){
    for(int i=0;i<6;++i)edges.emplace_back(i,(i+1)%6);
    return Checker(6,8,edges,{0,1}).run();
 }
 int n=0;for(int i=0;i<4;++i)for(int j=i+1;j<4;++j){
   edges.emplace_back(i,4+n);edges.emplace_back(j,4+n);++n;
 }
 if(mode=="k4")return Checker(10,15,edges,{0,4}).run((1<<10)-(1<<5));
 if(mode=="undirected")return Checker(10,15,edges,{0,4}).run();
 if(mode=="private"){edges.emplace_back(0,10);return Checker(11,16,edges,{0,10}).run((1<<10)-(1<<4));}
 return 2;
}
