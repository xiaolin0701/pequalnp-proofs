#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Word = std::uint32_t;
using Sep = unsigned __int128;
using Edge = std::pair<int,int>;
constexpr int nInputs=8, budget=12, cap=16;
struct Profile {
    std::vector<unsigned> positive, negative;
    std::array<Word,nInputs> raw{};
    Word target=0, mask=0, badPosTag=0;
    Sep pairs=0;
    explicit Profile(bool fixed) {
        const std::vector<Edge> edges={{1,2},{2,3},{3,4},{1,6},{2,7},{3,8},{5,7},{6,8},{5,8}};
        auto hit=[&](unsigned x){
            if(fixed && (x&((1<<0)|(1<<3)|(1<<4))))return true;
            for(auto [i,j]:edges) if((x>>(i-1))&(x>>(j-1))&1)return true;
            return false;
        };
        for(unsigned x=0;x<(1u<<nInputs);++x) {
            bool positiveValue=hit(x),extremal=true;
            for(int i=0;i<nInputs;++i) {
                bool on=x>>i&1;
                if(on==positiveValue && hit(x^(1u<<i))==positiveValue) extremal=false;
            }
            if(extremal) (positiveValue?positive:negative).push_back(x);
        }
        std::vector<unsigned> samples=positive;
        samples.insert(samples.end(),negative.begin(),negative.end());
        if(samples.size()>=32 || positive.size()*negative.size()>128) throw std::runtime_error("sample overflow");
        target=(Word(1)<<positive.size())-1;
        mask=(Word(1)<<samples.size())-1;
        pairs=~Sep(0)>>(128-positive.size()*negative.size());
        for(unsigned i=0;i<samples.size();++i) {
            for(int j=0;j<nInputs;++j) if(samples[i]>>j&1) raw[j]|=Word(1)<<i;
            if(!fixed && i>=positive.size() && (samples[i]&((1<<0)|(1<<3)|(1<<4))))
                badPosTag |= Word(1)<<i;
        }
    }
    Sep separates(Word w) const {
        const auto missing=(~w)>>positive.size() & ((Word(1)<<negative.size())-1);
        Sep s=0;
        for(unsigned i=0;i<positive.size();++i) if(w>>i&1) s|=Sep(missing)<<(i*negative.size());
        return s;
    }
};
using Values=std::array<Word,cap>;
struct CacheKey{
    Values values{};
    int count=0,rem=-1;
    bool value=false;
};
class Oracle {
    const Profile &p;
    std::vector<CacheKey> cache=std::vector<CacheKey>(1<<20);
    std::vector<Sep> table;
    const Sep sep(Word w) const {return table[w];}
public:
    std::uint64_t calls=0,hits=0;
    explicit Oracle(const Profile& p):p(p),table(p.mask+1) {
        for(Word w=0;w<=p.mask;++w)table[w]=p.separates(w);
    }
    bool can(Values a,int n,int rem) {
        ++calls;
        if(rem==0) return std::find(a.begin(),a.begin()+n,p.target)!=a.begin()+n;
        if(n>rem+1)return false;
        std::sort(a.begin(),a.begin()+n);
        std::fill(a.begin()+n,a.end(),0);
        std::uint64_t hash=rem;
        for(int i=0;i<n;++i)hash=(hash^(a[i]+0x9e3779b9u))*0x100000001b3ull;
        auto &slot=cache[(hash^(hash>>32))&(cache.size()-1)];
        if(slot.rem==rem && slot.count==n && slot.values==a){++hits;return slot.value;}
        auto store=[&](bool r){slot={a,n,rem,r};return r;};
        Sep unionAll=0;for(int t=0;t<n;++t)unionAll|=sep(a[t]);
        if(unionAll!=p.pairs)return store(false);
        for(int i=0;i<n;++i) for(int j=0;j<i;++j) {
            Sep other=0;for(int k=0;k<n;++k)if(k!=i&&k!=j)other|=sep(a[k]);
            for(auto w:{a[i]&a[j],a[i]|a[j]}) {
                if(w==p.target)return store(true);
                if(!w || w==p.mask || std::find(a.begin(),a.begin()+n,w)!=a.begin()+n)continue;
                for(int f=0;f<4;++f) {
                    if(n-1+bool(f&1)+bool(f&2)>rem)continue;
                    if((other|sep(w)|((f&1)?sep(a[i]):0)|((f&2)?sep(a[j]):0))!=p.pairs)continue;
                    Values b{};int m=0;
                    for(int k=0;k<n;++k)if((k!=i&&k!=j)||(k==i&&(f&1))||(k==j&&(f&2)))b[m++]=a[k];
                    b[m++]=w;
                    if(can(b,m,rem-1))return store(true);
                }
            }
        }
        return store(false);
    }
};
struct Signal { Word base,high; };
struct DualKey {
    std::array<std::uint64_t,cap> codes{};
    Word pos=0,neg=0;
    unsigned rem=0,n=0;
};
class Dual {
    Profile p0{false},p1{true};
    Oracle oracle{p0};
    std::vector<DualKey> cache=std::vector<DualKey>(1<<16);
    unsigned long long calls=0, successfulBase=0;
    bool guard;
    bool seen(const std::array<Signal,cap> &a,int n,int rem,Word pos,Word neg) {
        DualKey s;
        s.pos=pos;s.neg=neg;s.rem=rem+1;s.n=n;
        for(int k=0;k<n;++k)s.codes[k]=(std::uint64_t(a[k].base)<<32)|a[k].high;
        std::sort(s.codes.begin(),s.codes.begin()+n);
        std::uint64_t hash=pos^(std::uint64_t(neg)<<32)^rem;
        for(int k=0;k<n;++k)hash=(hash^(s.codes[k]+0x9e3779b9))*0x100000001b3ull;
        auto &slot=cache[(hash^(hash>>32))&(cache.size()-1)];
        if(slot.codes==s.codes && slot.pos==pos && slot.neg==neg && slot.rem==s.rem && slot.n==s.n) return true;
        slot=s;return false;
    }
    bool run(std::array<Signal,cap> a,int n,int rem,Word pos,Word neg) {
        ++calls;
        if(!rem || n>rem+1)return false;
        if(seen(a,n,rem,pos,neg))return false;
        for(int i=0;i<n;++i)for(int j=0;j<i;++j)for(int op=0;op<2;++op) {
            auto combine=[&](Word l,Word r){return op?l|r:l&r;};
            Word w=combine(a[i].base,a[j].base);
            if(!w || w==p0.mask)continue;
            bool duplicate=false; for(int k=0;k<n;++k)if(a[k].base==w)duplicate=true;
            if(duplicate)continue;
            for(int f=0;f<4;++f) {
                if(n-1+bool(f&1)+bool(f&2)>rem)continue;
                Values b{}; std::array<Signal,cap> next{};int m=0;
                for(int k=0;k<n;++k)if((k!=i&&k!=j)||(k==i&&(f&1))||(k==j&&(f&2))){b[m]=a[k].base;next[m++]=a[k];}
                b[m++]=w;
                if(rem==1 ? w!=p0.target : !oracle.can(b,m,rem-1)) continue;
                ++successfulBase;
                for(int ti=0;ti<3;++ti)for(int tj=0;tj<3;++tj) {
                    Word p=pos,q=neg;
                    auto transform=[&](Signal s,int t,Word &value){
                        value=s.high;
                        if(t==0)return true;
                        if(t==1) {
                            if((guard && (s.base&p0.badPosTag)) || (p && p!=s.base) || value==p1.mask)return false;
                            p=s.base;value=p1.mask;return true;
                        }
                        if((q && q!=s.base)||!value)return false;
                        q=s.base;value=0;return true;
                    };
                    Word u,v;
                    if(!transform(a[i],ti,u) || !transform(a[j],tj,v))continue;
                    Word wh=combine(u,v);
                    if(w==p0.target && wh==p1.target)return true;
                    next[m-1]={w,wh};
                    if(run(next,m,rem-1,p,q))return true;
                }
            }
        }
        return false;
    }
public:
    explicit Dual(bool useGuard):guard(useGuard){}
    bool check(){
        for(int i=0;i<nInputs;++i) {
            if(!p0.raw[i] || p0.raw[i]==p0.mask) throw std::logic_error("constant base input");
            for(int j=0;j<i;++j) if(p0.raw[i]==p0.raw[j]) throw std::logic_error("identical base inputs");
        }
        std::array<Signal,cap>a{};
        for(int i=0;i<nInputs;++i)a[i]={p0.raw[i],p1.raw[i]};
        std::cout<<"base="<<p0.positive.size()<<","<<p0.negative.size()<<" high="<<p1.positive.size()<<","<<p1.negative.size()<<std::endl;
        bool r=run(a,nInputs,budget,0,0);
        std::cout<<"dual="<<calls<<" base_candidates="<<successfulBase<<" oracle="<<oracle.calls
                 <<" oracle_hits="<<oracle.hits<<" result="<<(r?"SAT":"UNSAT")<<std::endl;
        return r;
    }
};
int main(int argc,char** argv){
    bool guard=argc==1;
    if(!guard && (argc!=2 || std::string(argv[1])!="no-guard"))return 2;
    return Dual(guard).check();
}
