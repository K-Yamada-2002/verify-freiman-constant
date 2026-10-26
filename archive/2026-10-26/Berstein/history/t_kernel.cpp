// Adapted from Freiman/src/graph_kernel.cpp (2026-10-01).
// Full-prefix F, T(binary,F), L, R, B2 types with absorbing past-3 flags.
// Closed invariant bands via uniform-overlap graphs, with integer interval arithmetic.
// All numbers denote dyadic rationals with denominator 2^48.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <sstream>
#include <queue>
#include <vector>
using namespace std;
using Z=int64_t;using W=__int128_t;constexpr Z D=Z(1)<<48;
Z down(W n,W d){assert(d>0);W q=n/d;if(n<0&&n%d)--q;assert(q>=numeric_limits<Z>::min()&&q<=numeric_limits<Z>::max());return Z(q);}
Z up(W n,W d){return -down(-n,d);}
struct I{Z l,h;};
I mul(I a,I b){array<W,4> v={W(a.l)*b.l,W(a.l)*b.h,W(a.h)*b.l,W(a.h)*b.h};return {down(*min_element(v.begin(),v.end()),D),up(*max_element(v.begin(),v.end()),D)};}
I divi(I a,I b){assert(b.l>0);array<Z,4> ll={down(W(a.l)*D,b.l),down(W(a.l)*D,b.h),down(W(a.h)*D,b.l),down(W(a.h)*D,b.h)};array<Z,4> hh={up(W(a.l)*D,b.l),up(W(a.l)*D,b.h),up(W(a.h)*D,b.l),up(W(a.h)*D,b.h)};return {*min_element(ll.begin(),ll.end()),*max_element(hh.begin(),hh.end())};}
I mix(I a,I b,Z t){I aa=mul(a,{D-t,D-t}),bb=mul(b,{t,t});return {aa.l+bb.l,aa.h+bb.h};}
// At fixed a,b, (a+R*b)/(1+R) is monotone in R. a,b enter with
// positive weights; their extrema therefore give a rigorous enclosure.
I sum_normalized(I a,I b,I R){
 if(a.l==a.h&&b.l==b.h&&a.l==b.l)return a;
 Z lo=numeric_limits<Z>::max(),hi=numeric_limits<Z>::min();
 for(Z r:{R.l,R.h}){
  auto x=divi({a.l+mul({r,r},{b.l,b.l}).l,a.h+mul({r,r},{b.h,b.h}).h},{D+r,D+r});
  lo=min(lo,x.l);hi=max(hi,x.h);
 }
 return {lo,hi};
}
struct Ext{int child=-1,spine=0,constant=0,x[2][2]{};I scale,eta[2];};
struct Side{int parity,anchor;I r;vector<I> tails,deltas;};
struct Pt{int x,y;};
struct Ends{vector<Pt> lo,hi;};
struct Vertex{int u,w,type;long double ml,mh;int left=0,right=0;Ends ends;};
struct Component{vector<int> front;int left,right;};
struct Rect{int u,w,child,lo,hi;};
int main(int argc,char**argv){
 if(argc!=3&&argc!=4){cerr<<"input.dat output.json [verify-existing.alive.bin]\n";return 2;}
 bool verification_only=argc==4;
 ifstream in(argv[1]);string magic;int S,E,L,H,T,P,root;
 in>>magic>>S>>E>>L>>H>>T>>P>>root;if(!in||magic!="BERSTEIN_T_GRAPH_V1")return 2;
 int B=H-L+1,N=S*S*B;vector<I> powers(B+1),width(S);assert(T==5);
 vector<array<int,3>> pairs(P);for(auto&p:pairs)in>>p[0]>>p[1]>>p[2];
 for(auto&v:powers)in>>v.l>>v.h;
 vector<vector<Ext>> ext(S,vector<Ext>(E));vector<Side> sides(S);
 for(int a=0;a<S;a++){in>>width[a].l>>width[a].h;
  auto&side=sides[a];int M;in>>side.parity>>side.r.l>>side.r.h>>side.anchor>>M;
  side.tails.resize(M);for(auto&v:side.tails)in>>v.l>>v.h;side.deltas.resize(M*M);
  for(int i=0;i<M;i++)for(int j=0;j<M;j++){
   if(i==j){side.deltas[i*M+j]={0,0};continue;}
   auto ratio=[&](I x){I result{numeric_limits<Z>::max(),numeric_limits<Z>::min()};
    for(Z r:{side.r.l,side.r.h}){I nu=mul({r,r},side.tails[side.anchor]),de=mul({r,r},x);
     I v=divi({D+nu.l,D+nu.h},{D+de.l,D+de.h});result.l=min(result.l,v.l);result.h=max(result.h,v.h);}
    return result;};
   I x=side.tails[i],y=side.tails[j];I v=mul({x.l-y.h,x.h-y.l},mul(ratio(x),ratio(y)));
   if(side.parity)v={-v.h,-v.l};side.deltas[i*M+j]=v;
  }
  for(auto&e:ext[a]){in>>e.child;if(e.child<0)continue;
   in>>e.spine>>e.constant>>e.scale.l>>e.scale.h;
   for(auto&v:e.eta)in>>v.l>>v.h;for(auto&lang:e.x)for(int&v:lang)in>>v;
   assert(e.scale.l>0&&e.scale.h>=e.scale.l);
  }
 }
 assert(in);vector<vector<Rect>> rects(N);vector<vector<int>> reverse(N);vector<I> actual_ratio(N);
 auto started=chrono::steady_clock::now();
 for(int a=0;a<S;a++)for(int b=0;b<S;b++)for(int k=0;k<B;k++){
  int cell=(a*S+b)*B+k;I scale={powers[k].l,powers[k+1].h};
  actual_ratio[cell]=mul(scale,divi(width[b],width[a]));
  for(auto pair:pairs){int u=pair[0],w=pair[1];const auto&x=ext[a][u];const auto&y=ext[b][w];
   if(x.child<0||y.child<0||(pair[2]&&(!x.spine||!y.spine)))continue;
   int lo,hi;
   if(x.constant&&x.constant==y.constant){lo=hi=k;}
   else{
    I ratio=divi(y.scale,x.scale);
    // Reject out-of-grid images before fixed-point multiplication; large
    // rejected scales need not fit the 64-bit dyadic representation.
    if(W(scale.l)*ratio.l<W(D)*powers.front().h ||
       W(scale.h)*ratio.h>W(D)*powers.back().l)continue;
    I mapped=mul(scale,ratio);
    // A bin is included unless disjointness is CERTAIN from the enclosures.
    // Ambiguity includes an extra bin, never silently discards one.
    if(mapped.l<powers.front().h||mapped.h>powers.back().l)continue;
    lo=0;while(lo+1<B&&powers[lo+1].h<=mapped.l)lo++;
    hi=B-1;while(hi>0&&powers[hi].l>=mapped.h)hi--;
   }
   int g=x.child*S+y.child;rects[cell].push_back({u,w,g,lo,hi});
   for(int j=lo;j<=hi;j++)reverse[g*B+j].push_back(cell);
  }
 }
 for(auto&v:reverse){sort(v.begin(),v.end());v.erase(unique(v.begin(),v.end()),v.end());}
 vector<unsigned char> alive(N*T,1),next;vector<int> prefix(S*S*T*(B+1));
 if(verification_only){ifstream saved(argv[3],ios::binary);saved.read(reinterpret_cast<char*>(alive.data()),alive.size());assert(saved.gcount()==(streamsize)alive.size());for(auto v:alive)assert(v<=1);char extra;assert(!saved.get(extra));}
 vector<int> work(N),marks(N,-1);iota(work.begin(),work.end(),0);int round=0;
 vector<int> history;string root_certificate="null";
 auto endpoints=[&](int a,int b,int u,int w,int t){
  Ends result;
  vector<pair<int,int>> channels;
  if(t==0)channels={{0,0}};if(t==1)channels={{1,0},{0,1}};
  if(t==2)channels={{1,0}};if(t==3)channels={{0,1}};if(t==4)channels={{1,1}};
  for(auto ch:channels){auto&x=ext[a][u];auto&y=ext[b][w];
   if(x.child<0||y.child<0||x.x[ch.first][0]<0||y.x[ch.second][0]<0)continue;
   result.lo.push_back({x.x[ch.first][0],y.x[ch.second][0]});
   result.hi.push_back({x.x[ch.first][1],y.x[ch.second][1]});
  }return result;
 };
 while(true){
  for(int g=0;g<S*S;g++)for(int t=0;t<T;t++){
   int o=(g*T+t)*(B+1);prefix[o]=0;
   for(int k=0;k<B;k++)prefix[o+k+1]=prefix[o+k]+!alive[(g*B+k)*T+t];
  }
  next=alive;int removed=0;vector<int> changed;
  for(int cell:work){
   bool any=false;for(int t=0;t<T;t++)any|=alive[cell*T+t];if(!any)continue;
   int g=cell/B,a=g/S,b=g%S,k=cell%B;vector<Vertex> vertices;
   I scale{powers[k].l,powers[k+1].h};
   auto ge=[&](Pt x,Pt y){
    auto aa=sides[a].deltas[x.x*sides[a].tails.size()+y.x];
    auto bb=sides[b].deltas[x.y*sides[b].tails.size()+y.y];
    return aa.l+mul(scale,bb).l>=0;
   };
   auto point=[&](int side,int id){auto&s=sides[side];
    long double r=(s.r.l+s.r.h)/(2.L*D),z=(s.tails[s.anchor].l+s.tails[s.anchor].h)/(2.L*D);
    long double x=(s.tails[id].l+s.tails[id].h)/(2.L*D);
    return (s.parity?-1:1)*(x-z)*(1+r*z)/(1+r*x);
   };
   auto value=[&](Pt x){return point(a,x.x)+(scale.l+scale.h)/(2.L*D)*point(b,x.y);};
   array<Ends,5> parents;for(int t=0;t<T;t++)parents[t]=endpoints(a,b,0,0,t);
   for(const auto&rect:rects[cell]){
    array<bool,5> used{};
    for(int t=0;t<T;t++){
     if(t>0&&used[0])break;if(t>1&&used[1])continue;if(t==4&&(used[2]||used[3]))continue;
     int o=(rect.child*T+t)*(B+1);
     if(prefix[o+rect.hi+1]!=prefix[o+rect.lo])continue;
     auto ee=endpoints(a,b,rect.u,rect.w,t);if(ee.lo.empty())continue;
     used[t]=true;
     long double ml=value(ee.lo[0]),mh=value(ee.hi[0]);
     for(auto x:ee.lo)ml=min(ml,value(x));for(auto x:ee.hi)mh=max(mh,value(x));
     vertices.push_back({rect.u,rect.w,t,ml,mh,0,0,ee});
    }
   }
   sort(vertices.begin(),vertices.end(),[](const Vertex&x,const Vertex&y){return x.ml<y.ml;});
   vector<Component> components;
   auto any_ge=[&](const vector<Pt>&x,const vector<Pt>&y){for(auto p:x)for(auto q:y)if(ge(p,q))return true;return false;};
   for(int i=0;i<(int)vertices.size();i++){
    auto&v=vertices[i];
    for(int t=0;t<T;t++)if(!parents[t].lo.empty()){
     bool left=true,right=true;
     for(auto p:parents[t].lo){bool ok=false;for(auto q:v.ends.lo)ok|=ge(p,q);left&=ok;}
     for(auto p:parents[t].hi){bool ok=false;for(auto q:v.ends.hi)ok|=ge(q,p);right&=ok;}
     if(left)v.left|=1<<t;if(right)v.right|=1<<t;
    }
    Component current{{i},v.left,v.right};
    for(int j=(int)components.size()-1;j>=0;j--){
     auto&c=components[j];if(vertices[c.front[0]].mh+1e-12L<v.ml)continue;
     bool connect=false;
     for(int f:c.front)if(any_ge(vertices[f].ends.hi,v.ends.lo)&&any_ge(v.ends.hi,vertices[f].ends.lo)){connect=true;break;}
     if(connect){current.left|=c.left;current.right|=c.right;current.front.insert(current.front.end(),c.front.begin(),c.front.end());components.erase(components.begin()+j);}
    }
    sort(current.front.begin(),current.front.end(),[&](int x,int y){return vertices[x].mh>vertices[y].mh;});
    if(current.front.size()>8)current.front.resize(8);components.push_back(std::move(current));
   }
   bool did=false;
   for(int t=0;t<T;t++)if(alive[cell*T+t]){
    bool covered=false;for(const auto&c:components)if((c.left&(1<<t))&&(c.right&(1<<t)))covered=true;
    if(!covered){next[cell*T+t]=0;removed++;did=true;}
   }
   if(did)changed.push_back(cell);
  }

  alive.swap(next);int total=accumulate(alive.begin(),alive.end(),0);history.push_back(total);
  cout<<"{\"round\":"<<round++<<",\"alive\":"<<total<<",\"removed\":"<<removed<<",\"root_types\":[";
  for(int t=0;t<T;t++)cout<<(t?",":"")<<(int)alive[root*T+t];
  cout<<"],\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}"<<endl;
  if(verification_only&&removed){cerr<<"The supplied family is not closed: "<<removed<<" states failed.\n";return 1;}
  if(!removed||!total)break;
  work.clear();for(int cell:changed)for(int parent:reverse[cell])if(marks[parent]!=round){marks[parent]=round;work.push_back(parent);}
 }
 ofstream bits(string(argv[2])+".alive.bin",ios::binary);bits.write(reinterpret_cast<const char*>(alive.data()),alive.size());
 int total=accumulate(alive.begin(),alive.end(),0);
 ofstream out(argv[2]);out<<"{\"arithmetic\":\"dyadic_integer_uniform_overlap_graph\",\"closed_family_found\":"<<(total?"true":"false")<<",\"surviving_states\":"<<total<<",\"root_types\":[";
 for(int t=0;t<T;t++)out<<(t?",":"")<<(int)alive[root*T+t];
 out<<"],\"round_counts\":[";for(int i=0;i<(int)history.size();i++)out<<(i?",":"")<<history[i];
 out<<"],\"verification_only\":"<<(verification_only?"true":"false")<<",\"root_certificate\":"<<root_certificate<<",\"freiman_ray_proved\":false}\n";
 return 0;
}
