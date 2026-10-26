// Closed invariant bands, using only integer interval arithmetic.
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
struct Ext{int child=-1,spine=0,constant=0;I scale,eta[2];};
struct Rect{int u,w,child,lo,hi;};
int main(int argc,char**argv){
 if(argc!=3){cerr<<"input.dat output.json\n";return 2;}
 ifstream in(argv[1]);string magic;int S,E,L,H,T,P,root;
 in>>magic>>S>>E>>L>>H>>T>>P>>root;if(!in||magic!="FREIMAN_DYADIC_V1")return 2;
 int B=H-L+1,N=S*S*B;vector<I> bands(T),powers(B+1),width(S);
 for(auto&v:bands)in>>v.l>>v.h;
 vector<array<int,3>> pairs(P);for(auto&p:pairs)in>>p[0]>>p[1]>>p[2];
 for(auto&v:powers)in>>v.l>>v.h;
 vector<vector<Ext>> ext(S,vector<Ext>(E));
 for(int a=0;a<S;a++){in>>width[a].l>>width[a].h;
  for(auto&e:ext[a]){in>>e.child;if(e.child<0)continue;
   in>>e.spine>>e.constant>>e.scale.l>>e.scale.h;
   for(auto&v:e.eta)in>>v.l>>v.h;
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
    I mapped=mul(scale,divi(y.scale,x.scale));
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
 vector<int> work(N),marks(N,-1);iota(work.begin(),work.end(),0);int round=0;
 vector<int> history;
 while(true){
  for(int g=0;g<S*S;g++)for(int t=0;t<T;t++){
   int o=(g*T+t)*(B+1);prefix[o]=0;
   for(int k=0;k<B;k++)prefix[o+k+1]=prefix[o+k]+!alive[(g*B+k)*T+t];
  }
  next=alive;int removed=0;vector<int> changed;
  for(int cell:work){
   bool any=false;for(int t=0;t<T;t++)any|=alive[cell*T+t];if(!any)continue;
   int g=cell/B,a=g/S,b=g%S;vector<I> intervals;
   for(const auto&rect:rects[cell]){
    vector<I> available;
    for(int t=0;t<T;t++){
     int o=(rect.child*T+t)*(B+1);
     if(prefix[o+rect.hi+1]==prefix[o+rect.lo]){
      available.push_back(bands[t]);if(t==0)break;
     }
    }
    sort(available.begin(),available.end(),[](I x,I y){return x.l<y.l;});vector<I> joined;
    for(I iv:available){if(!joined.empty()&&iv.l<=joined.back().h)joined.back().h=max(joined.back().h,iv.h);else joined.push_back(iv);}
    const auto&x=ext[a][rect.u];const auto&y=ext[b][rect.w];
    for(I band:joined){
     I left=sum_normalized(mix(x.eta[0],x.eta[1],band.l),mix(y.eta[0],y.eta[1],band.l),actual_ratio[cell]);
     I right=sum_normalized(mix(x.eta[0],x.eta[1],band.h),mix(y.eta[0],y.eta[1],band.h),actual_ratio[cell]);
     if(left.h<=right.l)intervals.push_back({left.h,right.l});
    }
   }
   sort(intervals.begin(),intervals.end(),[](I a,I b){return a.l<b.l;});vector<I> united;
   for(I iv:intervals){if(!united.empty()&&iv.l<=united.back().h)united.back().h=max(united.back().h,iv.h);else united.push_back(iv);}
   bool did=false;
   for(int t=0;t<T;t++)if(alive[cell*T+t]){
    bool covered=false;for(I iv:united)if(iv.l<=bands[t].l&&bands[t].h<=iv.h){covered=true;break;}
    if(!covered){next[cell*T+t]=0;removed++;did=true;}
   }
   if(did)changed.push_back(cell);
  }
  alive.swap(next);int total=accumulate(alive.begin(),alive.end(),0);history.push_back(total);
  cout<<"{\"round\":"<<round++<<",\"alive\":"<<total<<",\"removed\":"<<removed<<",\"root_types\":[";
  for(int t=0;t<T;t++)cout<<(t?",":"")<<(int)alive[root*T+t];
  cout<<"],\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}"<<endl;
  if(!removed||!total)break;
  work.clear();for(int cell:changed)for(int parent:reverse[cell])if(marks[parent]!=round){marks[parent]=round;work.push_back(parent);}
 }
 ofstream bits(string(argv[2])+".alive.bin",ios::binary);bits.write(reinterpret_cast<const char*>(alive.data()),alive.size());
 int total=accumulate(alive.begin(),alive.end(),0);
 ofstream out(argv[2]);out<<"{\"arithmetic\":\"dyadic_integer_intervals\",\"closed_family_found\":"<<(total?"true":"false")<<",\"surviving_states\":"<<total<<",\"root_types\":[";
 for(int t=0;t<T;t++)out<<(t?",":"")<<(int)alive[root*T+t];
 out<<"],\"round_counts\":[";for(int i=0;i<(int)history.size();i++)out<<(i?",":"")<<history[i];
 out<<"],\"freiman_ray_proved\":false}\n";
 return 0;
}
