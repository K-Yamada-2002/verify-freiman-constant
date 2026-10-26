// Numerical greatest-fixed-point discovery. Never a proof certificate.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
struct Ext {int child=-1,spine=0; double fl=0,fh=0,v[2][2][2]{};};
struct Rect {int u,w,child,lo,hi;};
struct Candidate {const Rect* rect;int type;double left=0,right=1;};
int main(int argc,char**argv){
 if(argc<3){cerr<<"input.dat output.json [excluded.txt]\n";return 2;}
 ifstream in(argv[1]); int S,E,L,H,maxlen,root,T,P;double base;
 in>>S>>E>>L>>H>>base>>maxlen>>root>>T>>P; if(!in)return 2;
 int B=H-L+1,N=S*S*B; vector<int> lengths(E);
 for(int&x:lengths)in>>x;
 vector<int> kind(T);vector<double> alpha(T),beta(T);
 for(int t=0;t<T;t++)in>>kind[t]>>alpha[t]>>beta[t];
 vector<array<int,3>> pairs(P);for(auto&p:pairs)in>>p[0]>>p[1]>>p[2];
 vector<vector<Ext>> ext(S,vector<Ext>(E));
 for(auto&side:ext)for(auto&e:side){in>>e.child;if(e.child<0)continue;
   in>>e.spine>>e.fl>>e.fh;for(auto&lang:e.v)for(auto&end:lang)for(double&x:end)in>>x;}
 vector<double> powers(B+1);for(int k=0;k<=B;k++)powers[k]=pow(base,L+k);
 vector<unsigned char> alive(N*T,1),next;vector<vector<Rect>> rects(N);
 for(int a=0;a<S;a++)for(int b=0;b<S;b++)for(int k=0;k<B;k++){
  int cell=(a*S+b)*B+k;
  for(auto uw:pairs){int u=uw[0],w=uw[1];
   const auto&x=ext[a][u];const auto&y=ext[b][w];if(x.child<0||y.child<0)continue;
   if(uw[2]&&(!x.spine||!y.spine))continue;
   double lo=powers[k]*y.fl/x.fh,hi=powers[k+1]*y.fh/x.fl;
   if(lo<powers[0]-1e-13||hi>powers[B]+1e-13)continue;
   int kl=max(0,(int)floor(log(lo)/log(base)+1e-11)-L);
   int kh=min(B-1,(int)ceil(log(hi)/log(base)-1e-11)-1-L);
   rects[cell].push_back({u,w,x.child*S+y.child,kl,kh});
  }
 }
 if(argc>3){ifstream banned(argv[3]);int id;while(banned>>id)if(id>=0&&id<N*T)alive[id]=0;}
 vector<vector<int>> reverse(N);
 for(int cell=0;cell<N;cell++)for(const auto&r:rects[cell])
  for(int k=r.lo;k<=r.hi;k++)reverse[r.child*B+k].push_back(cell);
 for(auto&v:reverse){sort(v.begin(),v.end());v.erase(unique(v.begin(),v.end()),v.end());}
 vector<int> work(N),marks(N,-1);iota(work.begin(),work.end(),0);
 auto interval=[&](const Ext&x,const Ext&y,int typ,int i,int j,double R){
  auto one=[&](int ka,int kb){return pair<double,double>{x.v[ka][i][0]+R*y.v[kb][j][0],x.v[ka][i][1]+R*y.v[kb][j][1]};};
  if(kind[typ]==5){auto iv=one(0,0);double len=iv.second-iv.first;return pair<double,double>{iv.first+alpha[typ]*len,iv.second-beta[typ]*len};}
  if(typ==0)return one(0,0);if(typ==2)return one(1,0);
  if(typ==3)return one(0,1);if(typ==4)return one(1,1);
  auto l=one(1,0),r=one(0,1);return pair<double,double>{min(l.first,r.first),max(l.second,r.second)};
 };
 vector<int> prefix(S*S*T*(B+1)); int round=0; vector<int> counts;
 auto start=chrono::steady_clock::now();
 while(true){
  for(int g=0;g<S*S;g++)for(int t=0;t<T;t++){
   int offset=(g*T+t)*(B+1);prefix[offset]=0;
   for(int k=0;k<B;k++)prefix[offset+k+1]=prefix[offset+k]+!alive[(g*B+k)*T+t];
  }
  next=alive;int removed=0;vector<int> changed;
  for(int cell:work){
   bool any=false;for(int t=0;t<T;t++)any|=alive[cell*T+t];if(!any)continue;
   int k=cell%B,g=cell/B,a=g/S,b=g%S;
   vector<Candidate> candidates;
   for(const auto&rect:rects[cell]){
    vector<bool> used(T,false);vector<pair<double,double>> bands;
    for(int t=0;t<T;t++){
     if(t>0&&used[0])break;
     if(t>1&&t<5&&used[1])continue;
     if(t==4&&(used[2]||used[3]))continue;
     int offset=(rect.child*T+t)*(B+1);
     if(prefix[offset+rect.hi+1]==prefix[offset+rect.lo]){
      if(kind[t]==5)bands.push_back({alpha[t],1-beta[t]});
      else candidates.push_back({&rect,t});used[t]=true;
     }
    }
    sort(bands.begin(),bands.end());vector<pair<double,double>> merged;
    for(auto iv:bands){if(!merged.empty()&&iv.first<=merged.back().second+1e-14)merged.back().second=max(merged.back().second,iv.second);else merged.push_back(iv);}
    for(auto iv:merged)candidates.push_back({&rect,-1,iv.first,iv.second});
   }
   vector<bool> pass(T);for(int t=0;t<T;t++)pass[t]=alive[cell*T+t];
   for(int i=0;i<2;i++)for(int j=0;j<2;j++)for(int z=0;z<2;z++){
    double R=powers[k+z];vector<pair<double,double>> ivs;ivs.reserve(candidates.size());
    for(const auto&c:candidates){
     auto iv=interval(ext[a][c.rect->u],ext[b][c.rect->w],max(0,c.type),i,j,R);
     if(c.type<0){double len=iv.second-iv.first;iv={iv.first+c.left*len,iv.first+c.right*len};}
     ivs.push_back(iv);
    }
    sort(ivs.begin(),ivs.end());vector<pair<double,double>> merged;
    for(auto iv:ivs){if(!merged.empty()&&iv.first<=merged.back().second+1e-12)merged.back().second=max(merged.back().second,iv.second);else merged.push_back(iv);}
    for(int t=0;t<T;t++)if(pass[t]){
     auto parent=interval(ext[a][0],ext[b][0],t,i,j,R);bool covered=false;
     for(auto iv:merged)if(iv.first<=parent.first+1e-12&&iv.second>=parent.second-1e-12){covered=true;break;}
     if(!covered)pass[t]=false;
    }
   }
   bool did=false;
   for(int t=0;t<T;t++)if(alive[cell*T+t]&&!pass[t]){next[cell*T+t]=0;removed++;did=true;}
   if(did)changed.push_back(cell);
  }
  alive.swap(next);int total=0;vector<int> kinds(T,0);
  for(int id=0;id<N*T;id++)if(alive[id]){total++;kinds[id%T]++;}
  counts.push_back(total);double sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cout<<"{\"round\":"<<round++<<",\"alive\":"<<total<<",\"removed\":"<<removed<<",\"root\":"<<(int)alive[root*T]<<",\"types\":[";
  for(int t=0;t<T;t++)cout<<(t?",":"")<<kinds[t];cout<<"],\"root_types\":[";for(int t=0;t<T;t++)cout<<(t?",":"")<<(int)alive[root*T+t];cout<<"],\"seconds\":"<<sec<<"}"<<endl;
  ofstream checkpoint(string(argv[2])+".alive.bin",ios::binary);checkpoint.write(reinterpret_cast<const char*>(alive.data()),alive.size());checkpoint.close();
  if(!removed||!total)break;
  work.clear();for(int cell:changed)for(int parent:reverse[cell])
   if(marks[parent]!=round){marks[parent]=round;work.push_back(parent);}
 }
 ofstream out(argv[2]);out<<"{\"proof_complete\":false,\"numerical_fixed_point\":true,\"root_survives\":"<<(alive[root*T]?"true":"false")<<",\"alive\":[";
 bool first=true;for(int id=0;id<N*T;id++)if(alive[id]){out<<(first?"":",")<<id;first=false;}
 out<<"],\"round_counts\":[";for(int i=0;i<(int)counts.size();i++)out<<(i?",":"")<<counts[i];out<<"]}\n";
}
