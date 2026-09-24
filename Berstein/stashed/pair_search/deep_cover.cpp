// Deep-check variant of refine_cover.cpp, permitting exponent 13.
// Integer-only outer-cylinder cover. Every accepted interval contains a real
// sum and has width <= epsilon; coverage proves distance, not membership.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
using T=int64_t; using I=__int128_t;
constexpr T S=1000000000000000LL;
constexpr I MAXI=I((~__uint128_t(0))>>1);
struct State {T lo,hi; int next[4];};
std::vector<State> states;
struct Cyl {T a=1,b=0,c=0,d=1,lo=0,hi=S; int state=0,depth=0;};
T endpoint(const Cyl& z,T tail,bool up) {
 I n=I(z.a)*tail+I(z.b)*S, d=I(z.c)*tail+I(z.d)*S;
 if(n<0 || d<=0 || n>MAXI/S) throw std::runtime_error("endpoint overflow");
 I q=n*S/d; if(up && n*S%d) ++q;
 if(q>std::numeric_limits<T>::max()) throw std::runtime_error("endpoint range");
 return T(q);
}
Cyl child(Cyl z,int k) {
 int state=states[z.state].next[k]; if(state<0) throw std::runtime_error("illegal child");
 I b=I(z.a)+I(k)*z.b,d=I(z.c)+I(k)*z.d;
 if(b>std::numeric_limits<T>::max() || d>std::numeric_limits<T>::max()) throw std::runtime_error("matrix overflow");
 z.a=z.b;z.b=T(b);z.c=z.d;z.d=T(d);z.state=state;++z.depth;
 auto s=states[state];
 z.lo=endpoint(z,z.depth%2?s.hi:s.lo,false);
 z.hi=endpoint(z,z.depth%2?s.lo:s.hi,true);
 return z;
}
Cyl prefix(const std::string& w) {Cyl z;for(char k:w) z=child(z,k-'0');return z;}
struct Cover {
 std::map<T,T> spans;
 bool contains(T a,T b) const {auto it=spans.upper_bound(a);return it!=spans.begin() && (--it)->second>=b;}
 void insert(T a,T b) {
  if(a>b)return;
  auto it=spans.lower_bound(a);
  if(it!=spans.begin()) {auto p=std::prev(it);if(p->second>=a)it=p;}
  while(it!=spans.end() && it->first<=b) {a=std::min(a,it->first);b=std::max(b,it->second);it=spans.erase(it);}
  spans.emplace(a,b);
 }
};
int main(int argc,char** argv) try {
 int exponent=argc>1?std::stoi(argv[1]):8;
 uint64_t budget=argc>2?std::stoull(argv[2]):2000000000ULL;
 if(exponent<1 || exponent>13)throw std::runtime_error("exponent range 1..13");
 T eps=S;for(int i=0;i<exponent;++i)eps/=10;
 int n;T targetlo,targethi;std::cin>>n>>targetlo>>targethi;states.resize(n);
 for(auto& s:states)std::cin>>s.lo>>s.hi>>s.next[1]>>s.next[2]>>s.next[3];
 int nl,nr;std::cin>>nl;std::vector<Cyl> left,right;std::string w;
 for(int i=0;i<nl;++i){std::cin>>w;left.push_back(prefix(w));}
 std::cin>>nr;for(int i=0;i<nr;++i){std::cin>>w;right.push_back(prefix(w));}
 if(!std::cin)throw std::runtime_error("invalid input");
 if(argc>3 && std::string(argv[3])=="--prefixes") {
  std::cout<<"[";bool first=true;
  for(auto z:left){if(!first)std::cout<<",";first=false;std::cout<<"["<<z.lo<<","<<z.hi<<"]";}
  std::cout<<"]\n";return 0;
 }
 std::vector<std::pair<Cyl,Cyl>> stack;
 for(auto u:left)for(auto v:right)stack.emplace_back(u,v);
 Cover cover;uint64_t visited=0,leaves=0;int depth=0;T maxwidth=0;
 auto start=std::chrono::steady_clock::now();
 while(!stack.empty() && visited<budget) {
  auto [u,v]=stack.back();stack.pop_back();++visited;
  T lo=u.lo+v.lo,hi=u.hi+v.hi,a=std::max(lo,targetlo),b=std::min(hi,targethi);
  if(a>b || cover.contains(a,b))continue;
  if(hi-lo<=eps){++leaves;maxwidth=std::max(maxwidth,hi-lo);depth=std::max({depth,u.depth,v.depth});cover.insert(a,b);continue;}
  bool split=u.hi-u.lo>=v.hi-v.lo;const Cyl& z=split?u:v;
  for(int k=3;k>=1;--k)if(states[z.state].next[k]>=0){Cyl c=child(z,k);stack.emplace_back(split?c:u,split?v:c);}
 }
 std::cout<<"{\"exponent\":"<<exponent<<",\"scale\":"<<S<<",\"visited\":"<<visited<<",\"leaves\":"<<leaves<<",\"max_width_units\":"<<maxwidth<<",\"max_depth\":"<<depth<<",\"complete\":"<<(stack.empty()?"true":"false")<<",\"covers_target\":"<<(cover.contains(targetlo,targethi)?"true":"false")<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<",\"covered\":[";
 bool first=true;for(auto [a,b]:cover.spans){if(!first)std::cout<<",";first=false;std::cout<<"["<<a<<","<<b<<"]";}std::cout<<"]}\n";
} catch(const std::exception& e){std::cerr<<e.what()<<"\n";return 1;}
