// Experimental suffix1-uniform family reduction. Sixth argument is geometry group ids.
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
#include <deque>
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
struct Ext{int child=-1,spine=0,constant=0,x[2]{};I scale,eta[2];};
struct Side{int parity,anchor;I r;vector<I> tails,deltas;};
struct End{int u,w;Z t;};
struct Vertex{int u,w;Z l,h;long double ml,mh;int left,right,child,binlo,binhi;};
struct Component{vector<int> front;int left,right;};
I difference(const Side&side,const Ext&x,Z tx,const Ext&y,Z ty){
 array<int,4> ids{};array<Z,4> coeff{};int n=0;
 auto add=[&](int id,Z c){for(int i=0;i<n;i++)if(ids[i]==id){coeff[i]+=c;return;}ids[n]=id;coeff[n++]=c;};
 add(x.x[0],D-tx);add(x.x[1],tx);add(y.x[0],-(D-ty));add(y.x[1],-ty);
 I result{0,0};int M=side.tails.size();
 for(int i=0;i<n;i++)while(coeff[i]>0){
  int j=0;while(j<n&&coeff[j]>=0)j++;assert(j<n);
  Z mass=min(coeff[i],-coeff[j]);I v=mul({mass,mass},side.deltas[ids[i]*M+ids[j]]);
  result.l+=v.l;result.h+=v.h;coeff[i]-=mass;coeff[j]+=mass;
 }
 for(int i=0;i<n;i++)assert(coeff[i]==0);
 return result;
}
struct Rect{int u,w,child,lo,hi;};
int main(int argc,char**argv){
 if(argc!=3&&argc!=4&&argc!=5&&argc!=6&&argc!=7){cerr<<"input.dat output.json [existing.alive.bin [prune [geometry-groups.txt [seconds]]]]\n";return 2;}
 bool verification_only=argc==4;
 double time_budget=argc==7?stod(argv[6]):0; bool reduction_completed=true;
 ifstream in(argv[1]);string magic;int S,E,L,H,T,P,root;
 in>>magic>>S>>E>>L>>H>>T>>P>>root;if(!in||magic!="FREIMAN_DYADIC_GRAPH_V1")return 2;
 int B=H-L+1,N=S*S*B;vector<I> bands(T),powers(B+1),width(S);
 for(auto&v:bands)in>>v.l>>v.h;
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
   for(auto&v:e.eta)in>>v.l>>v.h;in>>e.x[0]>>e.x[1];
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
 vector<unsigned char> alive(N*T,1);vector<int> prefix(S*S*T*(B+1));
 if(argc>=4){ifstream saved(argv[3],ios::binary);saved.read(reinterpret_cast<char*>(alive.data()),alive.size());assert(saved.gcount()==(streamsize)alive.size());for(auto v:alive)assert(v<=1);char extra;assert(!saved.get(extra));}
 
 vector<vector<int>> geometry_group(S*S);
 for(int g=0;g<S*S;g++)geometry_group[g]={g};
 if(argc>=6){
  ifstream groups(argv[5]); vector<int> ids(S*S); int n;
  groups>>n; vector<vector<int>> members(n);
  for(int g=0;g<S*S;g++){groups>>ids[g]; assert(ids[g]>=0&&ids[g]<n);members[ids[g]].push_back(g);}
  assert(groups); for(int g=0;g<S*S;g++)geometry_group[g]=members[ids[g]];
  // Each retained condition must apply uniformly to all finer geometries.
  for(const auto& group:members)for(int g:group)for(int j=0;j<B*T;j++)
   assert(alive[g*B*T+j]==alive[group.front()*B*T+j]);
 }
 vector<int> history;vector<Z> knots;string root_certificate="null";
 for(auto band:bands){knots.push_back(band.l);knots.push_back(band.h);}
 sort(knots.begin(),knots.end());knots.erase(unique(knots.begin(),knots.end()),knots.end());
 vector<pair<int,int>> band_indices;for(auto band:bands)band_indices.push_back({lower_bound(knots.begin(),knots.end(),band.l)-knots.begin(),lower_bound(knots.begin(),knots.end(),band.h)-knots.begin()});
 for(int g=0;g<S*S;g++)for(int t=0;t<T;t++){
  int o=(g*T+t)*(B+1);prefix[o]=0;
  for(int k=0;k<B;k++)prefix[o+k+1]=prefix[o+k]+!alive[(g*B+k)*T+t];
 }
 deque<int> pending;vector<unsigned char> queued(N,1);for(int i=0;i<N;i++)pending.push_back(i);
 int removed=0;long long visits=0;int initial_total=accumulate(alive.begin(),alive.end(),0);
 while(!pending.empty()){
  if(time_budget>0 && visits%1000==0 && chrono::duration<double>(chrono::steady_clock::now()-started).count()>time_budget){reduction_completed=false;break;}
  int cell=pending.front();pending.pop_front();queued[cell]=0;visits++;
   bool any=false;for(int t=0;t<T;t++)any|=alive[cell*T+t];if(!any)continue;
   int g=cell/B,a=g/S,b=g%S,k=cell%B;vector<Vertex> vertices;
   I scale{powers[k].l,powers[k+1].h};
   auto ge=[&](End x,End y){I aa=difference(sides[a],ext[a][x.u],x.t,ext[a][y.u],y.t),bb=difference(sides[b],ext[b][x.w],x.t,ext[b][y.w],y.t);return aa.l+mul(scale,bb).l>=0;};
   auto point=[&](int side,int e,Z theta){
    auto&s=sides[side];long double r=(s.r.l+s.r.h)/(2.L*D),anchor=(s.tails[s.anchor].l+s.tails[s.anchor].h)/(2.L*D);
    auto value=[&](int id){auto v=s.tails[id];long double x=(v.l+v.h)/(2.L*D);return (s.parity?-1:1)*(x-anchor)*(1+r*anchor)/(1+r*x);};
    return (1-theta/(long double)D)*value(ext[side][e].x[0])+theta/(long double)D*value(ext[side][e].x[1]);
   };
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
    for(I band:joined){
     long double ss=(scale.l+scale.h)/(2.L*D);
     long double ml=point(a,rect.u,band.l)+ss*point(b,rect.w,band.l);
     long double mh=point(a,rect.u,band.h)+ss*point(b,rect.w,band.h);
     vertices.push_back({rect.u,rect.w,band.l,band.h,ml,mh,0,0,rect.child,rect.lo,rect.hi});
    }
   }
   sort(vertices.begin(),vertices.end(),[](const Vertex&x,const Vertex&y){return x.ml<y.ml;});
   vector<Component> components;
   vector<pair<int,int>> root_edges;
   for(int i=0;i<(int)vertices.size();i++){
    auto&v=vertices[i];End lower{v.u,v.w,v.l},upper{v.u,v.w,v.h};
    int lo=0,hi=knots.size()-1;v.left=knots.size();v.right=-1;
    while(lo<=hi){int mid=(lo+hi)/2;if(ge({0,0,knots[mid]},lower)){v.left=mid;hi=mid-1;}else lo=mid+1;}
    lo=0;hi=knots.size()-1;
    while(lo<=hi){int mid=(lo+hi)/2;if(ge(upper,{0,0,knots[mid]})){v.right=mid;lo=mid+1;}else hi=mid-1;}
    Component current{{i},v.left,v.right};
    for(int j=(int)components.size()-1;j>=0;j--){
     auto&c=components[j];if(vertices[c.front[0]].mh+1e-12L<v.ml)continue;
     bool connect=false;
     for(int f:c.front){auto&z=vertices[f];if(ge({z.u,z.w,z.h},lower)&&ge(upper,{z.u,z.w,z.l})){connect=true;if(cell==root)root_edges.push_back({i,f});break;}}
     if(connect){current.left=min(current.left,c.left);current.right=max(current.right,c.right);current.front.insert(current.front.end(),c.front.begin(),c.front.end());components.erase(components.begin()+j);}
    }
    sort(current.front.begin(),current.front.end(),[&](int x,int y){return vertices[x].mh>vertices[y].mh;});
    if(current.front.size()>8)current.front.resize(8);components.push_back(std::move(current));
   }
   bool did=false;
   for(int t=0;t<T;t++)if(alive[cell*T+t]){
    bool covered=false;for(const auto&c:components)if(c.left<=band_indices[t].first&&band_indices[t].second<=c.right){covered=true;break;}
    if(!covered){
     for(int gg:geometry_group[g]){
      int affected=gg*B+k;
      if(!alive[affected*T+t])continue;
      alive[affected*T+t]=0;removed++;did=true;
      int offset=(gg*T+t)*(B+1);for(int j=k+1;j<=B;j++)prefix[offset+j]++;
      for(int parent:reverse[affected])if(!queued[parent]){queued[parent]=1;pending.push_back(parent);}
     }
    }
   }
   if(did){
    if(verification_only){cerr<<"The supplied family is not closed.\n";return 1;}
    for(int parent:reverse[cell])if(!queued[parent]){queued[parent]=1;pending.push_back(parent);}
   }
   if(cell==root){
    root_certificate="null";
    for(int t=0;t<T;t++)if(alive[cell*T+t]){
     vector<vector<int>> adj(vertices.size());for(auto e:root_edges){adj[e.first].push_back(e.second);adj[e.second].push_back(e.first);}
     vector<int> pred(vertices.size(),-2);queue<int> bfs;
     for(int i=0;i<(int)vertices.size();i++)if(vertices[i].left<=band_indices[t].first){pred[i]=-1;bfs.push(i);}
     int finish=-1;
     while(!bfs.empty()){
      int i=bfs.front();bfs.pop();if(vertices[i].right>=band_indices[t].second){finish=i;break;}
      for(int j:adj[i])if(pred[j]==-2){pred[j]=i;bfs.push(j);}
     }
     assert(finish>=0);vector<int> path;for(int i=finish;i>=0;i=pred[i])path.push_back(i);std::reverse(path.begin(),path.end());
     ostringstream proof;proof<<"{\"parent_type\":"<<t<<",\"chain\":[";bool first=true;
     for(int i:path){auto&v=vertices[i];proof<<(first?"":",")<<"{\"extension_indices\":["<<v.u<<","<<v.w<<"],\"joined_band\":["<<v.l<<","<<v.h<<"],\"destination_geometry\":"<<v.child<<",\"scale_bins\":["<<v.binlo+L<<","<<v.binhi+L<<"],\"band_types\":[";bool ft=true;
      for(int tt=0;tt<T;tt++){int o=(v.child*T+tt)*(B+1);if(bands[tt].l>=v.l&&bands[tt].h<=v.h&&prefix[o+v.binhi+1]==prefix[o+v.binlo]){proof<<(ft?"":",")<<tt;ft=false;}}
      proof<<"]}";first=false;
     }
     proof<<"]}";root_certificate=proof.str();break;
    }
   }
  if(visits%10000==0){
   cout<<"{\"visits\":"<<visits<<",\"alive\":"<<initial_total-removed<<",\"pending\":"<<pending.size()<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}"<<endl;
  }
 }
 history.push_back(initial_total-removed);
 cout<<"{\"fixed_point\":"<<(reduction_completed?"true":"false")<<",\"visits\":"<<visits<<",\"alive\":"<<initial_total-removed<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}"<<endl;
 ofstream bits(string(argv[2])+".alive.bin",ios::binary);bits.write(reinterpret_cast<const char*>(alive.data()),alive.size());
 int total=accumulate(alive.begin(),alive.end(),0);
 if(!reduction_completed)root_certificate="null";
 ofstream out(argv[2]);out<<"{\"arithmetic\":\"dyadic_integer_uniform_overlap_graph\",\"closed_family_found\":"<<(total&&reduction_completed?"true":"false")<<",\"reduction_completed\":"<<(reduction_completed?"true":"false")<<",\"surviving_states\":"<<total<<",\"root_types\":[";
 for(int t=0;t<T;t++)out<<(t?",":"")<<(int)alive[root*T+t];
 out<<"],\"round_counts\":[";for(int i=0;i<(int)history.size();i++)out<<(i?",":"")<<history[i];
 out<<"],\"verification_only\":"<<(verification_only?"true":"false")<<",\"root_certificate\":"<<root_certificate<<",\"freiman_ray_proved\":false}\n";
 return 0;
}
