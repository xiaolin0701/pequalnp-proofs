// Search bounded gate edits of 27-gate star circuits. Inputs 0..6 are points,
// inputs 7..13 are lines, and each point x lies on lines x, x-1, x-3 modulo 7.
// Build with c++ -std=c++17 -O3 local_search.cpp -o local_search.
// Arguments: seed, number of star circuits, maximum number of edited gates, optionally a near-circuit corpus.
// Alternatively, --distributed seed trials checks a deletion plus one gate edit
// around each of the corresponding 28-gate distributive constructions.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <optional>
#include <sstream>
#include <string>
#include <random>
#include <set>
#include <tuple>
#include <vector>
using U=uint64_t;
constexpr int n=14,s=27;
struct Gate {int a,b;bool disjunction;};
using Program=std::array<Gate,s>;
using Wires=std::array<U,n+s>;
using Marks=std::array<unsigned,n+s>;
struct Frontier {Wires inputs{};U target=0,domain=0;};

bool incident(int a,int b){return (a-b+7)%7==0||(a-b+7)%7==1||(a-b+7)%7==3;}
bool edge(int x){
    for(int a=0;a<7;++a) for(int b=0;b<7;++b)
        if(incident(a,b)&&(x&(1<<a))&&(x&(1<<(7+b)))) return true;
    return false;
}
Frontier frontier(){
    Frontier f;int row=0;
    for(int x=0;x<(1<<n);++x){bool y=edge(x),extreme=true;
        for(int j=0;j<n;++j)if(bool(x&(1<<j))==y&&edge(x^(1<<j))==y)extreme=false;
        if(!extreme)continue;
        U bit=U(1)<<row++; f.domain|=bit;if(y)f.target|=bit;
        for(int j=0;j<n;++j)if(x&(1<<j))f.inputs[j]|=bit;
    }
    if(row!=58||__builtin_popcountll(f.target)!=21)abort();
    return f;
}
U value(const Wires &w,Gate g){return g.disjunction?w[g.a]|w[g.b]:w[g.a]&w[g.b];}
void run(Program const& p,Wires& w,int start){
    for(int i=start;i<s;++i)w[n+i]=value(w,p[i]);
}

struct Degrees {
    Marks present{}, repeated{};
    Degrees(){for(int i=0;i<n;++i)present[i]=1u<<i;}
    void step(int i,Gate g) {
        present[n+i]=present[g.a]|present[g.b];
        repeated[n+i]=repeated[g.a]|repeated[g.b];
        if(!g.disjunction)repeated[n+i]|=present[g.a]&present[g.b];
    }
    void run(Program const& p,int from=0){for(int i=from;i<s;++i)step(i,p[i]);}
};
bool pair(unsigned d){
    for(int a=0;a<7;++a) for(int b=0;b<7;++b)
        if((d&(1u<<a))&&(d&(1u<<(7+b)))&&incident(a,b))return true;
    return false;
}
Program star(std::mt19937 &rng,int index) {
    bool dual=index%2; Program p{};int size=0;
    auto gate=[&](int a,int b,bool op){p[size]={a,b,op};return n+size++;};
    std::vector<int> centers{0,1,2,3,4,5,6},terms;
    if(index>=2)std::shuffle(centers.begin(),centers.end(),rng);
    for(auto v:centers){std::vector<int> ns;
        for(int j=0;j<7;++j)if(dual?incident(j,v):incident(v,j))ns.push_back(dual?j:7+j);
        if(index>=2)std::shuffle(ns.begin(),ns.end(),rng);
        int first=gate(ns[0],ns[1],true);
        terms.push_back(gate(dual?v+7:v,gate(first,ns[2],true),false));
    }
    while(terms.size()>1){if(index>=2)std::shuffle(terms.begin(),terms.end(),rng);
        int a=terms.back();terms.pop_back();int b=terms.back();terms.pop_back();terms.push_back(gate(a,b,true));}
    if(size!=s)abort();return p;
}
struct Search {
    Frontier f;Program p;uint64_t verified=0,queries=0,any_repeat=0;
    bool verify() {
        for(int i=0;i<s;++i) if(p[i].a==p[i].b) return false;
        Degrees d;d.run(p);++verified;if(d.repeated.back())++any_repeat;if(!pair(d.repeated.back()))return false;
        for(int x=0;x<(1<<n);++x){Wires w{};for(int j=0;j<n;++j)w[j]=(x>>j)&1;
            run(p,w,0);if(bool(w.back())!=edge(x))abort();}
        printf("witness repeated mask %u\n",d.repeated.back());
        for(auto g:p)printf("%d %c %d\n",g.a,g.disjunction?'|':'&',g.b);
        fflush(stdout);return true;
    }
    bool search(Wires const&w,Degrees const&d,int start,int remaining) {
        if(remaining==1){
            for(int j=start;j<s;++j){Wires lo=w,hi=w;lo[n+j]=0;hi[n+j]=f.domain;
                run(p,lo,j+1);run(p,hi,j+1);++queries;
                if((lo.back()&~f.target)||(f.target&~hi.back()))continue;
                U yes=f.target&~lo.back(),no=~f.target&hi.back();
                auto saved=p[j];
                for(int a=0;a<n+j;++a)for(int b=a+1;b<n+j;++b){
                    auto consider=[&](bool disj){Gate g{a,b,disj};U v=value(w,g);
                        if((v&yes)!=yes||(v&no))return false;p[j]=g;return verify();};
                    if(consider(false)||consider(true))return true;
                }
                p[j]=saved;
            }
            return false;
        }
        for(int j=start;j<=s-remaining;++j){
            std::set<std::tuple<U,unsigned,unsigned>> seen;
            seen.emplace(w[n+j],d.present[n+j],d.repeated[n+j]);auto saved=p[j];
            for(int a=0;a<n+j;++a)for(int b=a+1;b<n+j;++b)for(bool op:{false,true}){
                Gate g{a,b,op};U col=value(w,g);Degrees temp=d;temp.step(j,g);
                if(!seen.emplace(col,temp.present[n+j],temp.repeated[n+j]).second)continue;
                Wires post=w;post[n+j]=col;run(p,post,j+1);temp.run(p,j+1);p[j]=g;
                if(search(post,temp,j+1,remaining-1))return true;
            }
            p[j]=saved;
        }
        return false;
    }
};
// Corpus format: one program per line as 27 tokens such as "0&7 1|8 ...".
std::optional<Program> read_program(std::ifstream &input) {
    std::string line;
    if(!std::getline(input,line)) return std::nullopt;
    std::istringstream row(line); Program p;
    for(int i=0;i<s;++i) {
        char op;int a,b;
        if(!(row>>a>>op>>b) || (op!='&' && op!='|') || a==b ||
           std::min(a,b)<0 || std::max(a,b)>=n+i) std::abort();
        p[i]={a,b,op=='|'};
    }
    std::string extra;if(row>>extra)std::abort();
    return p;
}
// For an exceptional center p, distribute R OR (p AND N(p)) as
// (R OR p) AND (R OR N(p)), where R is the union of all other stars.
using Larger=std::array<Gate,28>;
Larger lift(std::mt19937& rng, int index){
    Larger p;int size=0;auto g=[&](int a,int b,bool o){p[size]={a,b,o};return 14+size++;};
    int center=rng()%7;bool dual=index%2;
    std::vector<int> seq={0,1,2,3,4,5,6},stars;
    std::shuffle(seq.begin(),seq.end(),rng);int nb=-1;
    for(int i:seq){std::vector<int> js;
      for(int j=0;j<7;++j)if(dual?incident(j,i):incident(i,j))js.push_back(dual?j:7+j);
      std::shuffle(js.begin(),js.end(),rng);
      const int nsum=g(g(js[0],js[1],1),js[2],1);
      if(i==center)nb=nsum;else stars.push_back(g(dual?7+i:i,nsum,0));
    }
    while(stars.size()>1){std::shuffle(stars.begin(),stars.end(),rng);int a=stars.back();stars.pop_back();int b=stars.back();stars.pop_back();stars.push_back(g(a,b,1));}
    int R=stars[0],left=g(R,dual?7+center:center,1),right=g(R,nb,1);
    g(left,right,0);if(size!=28)abort();return p;
}
int test_distributed(int seed_value, int num) {
 std::mt19937 rng(seed_value);const auto f=frontier();
 uint64_t global_valid=0,global_queries=0,legal=0;
 for(int seed=0;seed<num;++seed){auto src=lift(rng,seed);
   for(int drop=0;drop<27;++drop)for(int alias=0;alias<14+drop;++alias) {
     auto id=[&](int i){return i==14+drop?alias:i>14+drop?i-1:i;};
     Program p;int invalid=0; for(int i=0,j=0;i<28;++i)if(i!=drop) {
       const auto g=src[i];int a=id(g.a),b=id(g.b);p[j++]={a,b,g.disjunction};invalid+=(a==b);}
     if(invalid>1)continue;++legal;
     auto w=f.inputs;run(p,w,0);Degrees d;d.run(p);Search search{f,p};
     if(!invalid && w.back()==f.target && pair(d.repeated.back())){search.verify();return 0;}
     if(search.search(w,d,0,1))return 0;
     global_valid+=search.verified;global_queries+=search.queries;
   }
 }
 printf("%d exact 28-gate starts, %llu admissible deletions, %llu final cone checks, %llu frontier matches, zero marked witnesses\n", num,(unsigned long long)legal,(unsigned long long)global_queries,(unsigned long long)global_valid);
 return 0;
}

int main(int argc,char**argv){
    if(argc==4 && std::string(argv[1])=="--distributed")
        return test_distributed(std::atoi(argv[2]),std::atoi(argv[3]));
    if(argc!=4 && argc!=5)return 2;
    const bool from_file=argc==5; std::ifstream input;
    if(from_file){input.open(argv[4]);if(!input)return 2;}
    std::mt19937 rng(std::atoi(argv[1]));int count=std::atoi(argv[2]),k=std::atoi(argv[3]);
    auto f=frontier();uint64_t valid=0,queries=0,repeats=0;
    for(int i=0;i<count;++i){auto given=from_file?read_program(input):std::optional<Program>(star(rng,i));
        if(!given) return 2;
        auto p=*given; Wires w=f.inputs;run(p,w,0);Degrees d;d.run(p);
        if(from_file) {
            if(__builtin_popcountll(w.back()^f.target)>2 || !pair(d.repeated.back()))abort();
        }else if(w.back()!=f.target || d.repeated.back())abort();
        Search x{f,p};
        for(int r=1;r<=k;++r)if(x.search(w,d,0,r))return 0;
        valid+=x.verified;queries+=x.queries;repeats+=x.any_repeat;
        if(i<2||i%10==9)fprintf(stderr,"%d seeds, %llu matching-frontier gate placements, %llu cone queries\n",
                i+1,(unsigned long long)valid,(unsigned long long)queries);
    }
    printf("no witness in %d seeded circuits' %d-edit neighborhoods; %llu frontier matches; %llu cone queries; %llu matches repeated at least one input\n",
           count,k,(unsigned long long)valid,(unsigned long long)queries,(unsigned long long)repeats);
    return 0;
}
