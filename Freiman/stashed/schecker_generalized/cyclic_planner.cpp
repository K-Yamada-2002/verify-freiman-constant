// Floating candidate planner only. Every emitted graph is replayed in Q(sqrt(462)).
// Python supplies legal transitions, whole-image destinations and endpoint labels.
#include <algorithm>
#include <array>
#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
struct Pt { double x,y; bool operator<(const Pt& b)const{return tie(x,y)<tie(b.x,b.y);} };
using Key=array<int,3>;
struct Cell {
    int p;double rl,rh,sl,sh,ql,qh,a,b;vector<Pt> points;vector<Key> local,pending,failed;
    double direction=1.;
    double value(Pt z)const {
        double r=(rl+rh)/2,s=(sl+sh)/2,q=(ql+qh)/2;
        return direction*(pow(1+r*a,2)*z.x/(1+r*z.x)+p*q*pow(1+s*b,2)*z.y/(1+s*z.y));
    }
    bool ge(Pt x,Pt y)const {
        if(x.x==y.x && x.y==y.y)return true;
        if(direction<0)swap(x,y);
        auto delta=[](double a,double x,double y,double r){return (x-y)*pow(1+a*r,2)/((1+x*r)*(1+y*r));};
        double dl=min(delta(a,x.x,y.x,rl),delta(a,x.x,y.x,rh));
        double d0=delta(b,x.y,y.y,sl),d1=delta(b,x.y,y.y,sh);
        double dr=p>0?min(d0,d1):-max(d0,d1);
        return dl+(dr>=0?ql:qh)*dr>=-2e-14;
    }
};
struct Dep{int cid;vector<int> ids;};
struct Move{vector<Pt> mapped;vector<int> order,group;vector<Dep> deps;vector<pair<int,int>> shapes;};
struct Offer{int cost,move,lo,hi;double upper;Pt next;vector<Key> keys;};
map<int,Cell> cells;vector<Move> moves;set<Key> rejected,local,pending;Key current;
bool use_reuse,return_offers,reuse_pending,restricted_shapes,min_cost_cover;int variants;long reused=0,pruned=0;
bool avoid(Key k) {
    const auto& c=cells.at(k[0]);
    for(auto old:c.failed)
        if(c.ge(c.points[old[1]],c.points[k[1]])&&c.ge(c.points[k[2]],c.points[old[2]])){
            ++pruned;return true;
        }
    return false;
}
Key reuse(Key k) {
    if(!use_reuse)return k;
    const auto& c=cells.at(k[0]);
    auto contains=[&](Key old){return c.ge(c.points[k[1]],c.points[old[1]])&&c.ge(c.points[old[2]],c.points[k[2]]);};
    if(k[0]==current[0]&&contains(current)){reused+=k!=current;return current;}
    for(auto it=c.local.rbegin();it!=c.local.rend();++it)
        if(contains(*it)){reused+=k!=*it;return *it;}
    for(auto it=c.pending.rbegin();it!=c.pending.rend();++it)
        if(contains(*it)){reused+=k!=*it;return *it;}
    return k;
}
vector<Offer> candidates(Pt contact,bool all=false) {
    vector<Offer> result;const auto& parent=cells.at(current[0]);double value=parent.value(contact);
    for(int mi=0;mi<(int)moves.size();++mi){
        const auto& m=moves[mi];map<int,vector<int>> lower;
        set<pair<int,int>> seen;
        auto offer=[&](int lo,int hi){
            double upper=parent.value(m.mapped[hi]);
            if(lo==hi||seen.count({lo,hi})||m.group[lo]<0||m.group[lo]!=m.group[hi]
                ||upper<=parent.value(m.mapped[lo])+1e-13
                ||(!all&&(upper<=value+1e-13||!parent.ge(contact,m.mapped[lo])
                ||!parent.ge(m.mapped[hi],contact)))||!parent.ge(m.mapped[hi],m.mapped[lo]))return false;
            vector<Key> keys;
            for(const auto& dep:m.deps){
                const auto& c=cells.at(dep.cid);int a=dep.ids[lo],b=dep.ids[hi];
                if(c.value(c.points[a])>c.value(c.points[b]))swap(a,b);
                if(a==b||!c.ge(c.points[b],c.points[a]))return false;
                Key k=reuse({dep.cid,a,b});
                if(rejected.count(k)||avoid(k))return false;keys.push_back(k);
            }
            set<Key> unique(keys.begin(),keys.end());int cost=0;
            if(use_reuse)for(auto k:unique)if(k!=current&&!local.count(k))
                cost+=reuse_pending&&!pending.count(k)?2:1;
            result.push_back({cost,mi,lo,hi,upper,m.mapped[hi],move(keys)});
            seen.insert({lo,hi});return true;
        };
        if(return_offers&&use_reuse)for(const auto& dep:m.deps){
            vector<int> inverse(cells.at(dep.cid).points.size(),-1);
            for(int i=0;i<(int)dep.ids.size();++i)inverse.at(dep.ids[i])=i;
            vector<Key> known;if(dep.cid==current[0])known.push_back(current);
            const auto& existing=cells.at(dep.cid).local;
            known.insert(known.end(),existing.begin(),existing.end());
            const auto& waiting=cells.at(dep.cid).pending;
            known.insert(known.end(),waiting.begin(),waiting.end());
            for(auto old:known){
                int lo=inverse.at(old[1]),hi=inverse.at(old[2]);
                if(lo<0||hi<0)continue;
                if(parent.value(m.mapped[lo])>parent.value(m.mapped[hi]))swap(lo,hi);
                offer(lo,hi);
            }
        }
        if(restricted_shapes){
            for(auto pair:m.shapes){
                int lo=pair.first,hi=pair.second;
                if(parent.value(m.mapped[lo])>parent.value(m.mapped[hi]))swap(lo,hi);
                offer(lo,hi);
            }
            continue;
        }
        for(auto it=m.order.rbegin();it!=m.order.rend();++it)
            if(m.group[*it]>=0&&parent.ge(contact,m.mapped[*it]))lower[m.group[*it]].push_back(*it);
        int count=0;
        for(auto hit=m.order.rbegin();hit!=m.order.rend();++hit){
            int hi=*hit;double upper=parent.value(m.mapped[hi]);
            if(upper<=value+1e-13||!lower.count(m.group[hi])||!parent.ge(m.mapped[hi],contact))continue;
            for(int lo:lower.at(m.group[hi])){
                if(seen.count({lo,hi})||offer(lo,hi)){++count;break;}
            }
            if(count>=variants)break;
        }
    }
    stable_sort(result.begin(),result.end(),[](const Offer&a,const Offer&b){return a.cost!=b.cost?a.cost<b.cost:a.upper>b.upper;});
    return result;
}
struct Frame {Pt point;vector<Offer> offers;size_t pos=0;bool prepared=false;};
int main(){
    ios::sync_with_stdio(false);cin.tie(nullptr);
    for(;;){
    int nc,nm;if(!(cin>>nc))return 0;
    cells.clear();moves.clear();rejected.clear();local.clear();pending.clear();reused=0;pruned=0;
    cin>>nm>>variants>>use_reuse>>return_offers>>restricted_shapes>>min_cost_cover>>current[0]>>current[1]>>current[2];
    for(int i=0;i<nc;++i){
        int cid,n;Cell c;cin>>cid>>c.p>>c.rl>>c.rh>>c.sl>>c.sh>>c.ql>>c.qh>>c.a>>c.b;
#ifdef CORRELATED_CHARTS
        cin>>c.direction;
#endif
        cin>>n;
        c.points.resize(n);for(auto& z:c.points)cin>>z.x>>z.y;cells[cid]=move(c);
    }
    int n;cin>>n;for(int i=0;i<n;++i){Key k;cin>>k[0]>>k[1]>>k[2];rejected.insert(k);}
    cin>>n;for(int i=0;i<n;++i){Key k;cin>>k[0]>>k[1]>>k[2];local.insert(k);cells.at(k[0]).local.push_back(k);}
    cin>>reuse_pending>>n;for(int i=0;i<n;++i){Key k;cin>>k[0]>>k[1]>>k[2];pending.insert(k);cells.at(k[0]).pending.push_back(k);}
    cin>>n;for(int i=0;i<n;++i){Key k;cin>>k[0]>>k[1]>>k[2];cells.at(k[0]).failed.push_back(k);}
    moves.resize(nm);
    for(auto& m:moves){
        int count,nd;cin>>count>>nd;m.mapped.resize(count);m.order.resize(count);m.group.resize(count);
        for(auto& z:m.mapped)cin>>z.x>>z.y;
        for(int& i:m.order)cin>>i;for(int& i:m.group)cin>>i;
        m.deps.resize(nd);for(auto& d:m.deps){cin>>d.cid;d.ids.resize(count);for(int& i:d.ids)cin>>i;}
        int ns;cin>>ns;m.shapes.resize(ns);for(auto& pair:m.shapes)cin>>pair.first>>pair.second;
    }
    if(!cin){cerr<<"incomplete planner input\n";return 2;}
    const auto& c=cells.at(current[0]);Pt end=c.points[current[2]];
    vector<Frame> stack{{c.points[current[1]],{},0,false}};vector<Offer> path;set<Pt> failed;bool found=false;
    if(min_cost_cover&&restricted_shapes){
        Pt start=c.points[current[1]];
        auto offers=candidates(start,true);
        stable_sort(offers.begin(),offers.end(),[](const Offer&a,const Offer&b){return a.upper<b.upper;});
        using Cost=array<int,3>;const Cost infinity={numeric_limits<int>::max()/4,0,0};
        vector<Cost> distance(offers.size(),infinity);vector<int> previous(offers.size(),-2);
        int finish=-1;
        for(int i=0;i<(int)offers.size();++i){
            const auto& o=offers[i];Pt lower=moves[o.move].mapped[o.lo];
            set<Key> unique(o.keys.begin(),o.keys.end());Cost weight={o.cost,(int)unique.size(),1};
            if(o.upper>c.value(start)+1e-13&&c.ge(start,lower)&&c.ge(o.next,start)){
                distance[i]=weight;previous[i]=-1;
            }
            for(int j=0;j<i;++j)if(previous[j]!=-2&&o.upper>offers[j].upper+1e-13
                &&c.ge(offers[j].next,lower)&&c.ge(o.next,offers[j].next)){
                Cost candidate=distance[j];for(int k=0;k<3;++k)candidate[k]+=weight[k];
                if(candidate<distance[i]){distance[i]=candidate;previous[i]=j;}
            }
            if(previous[i]!=-2&&c.ge(o.next,end)&&(finish<0||distance[i]<distance[finish]))finish=i;
        }
        if(finish>=0){
            found=true;for(int i=finish;i!=-1;i=previous[i])path.push_back(offers[i]);
            reverse(path.begin(),path.end());
        }
        stack.clear();
    }
    while(!stack.empty()){
        auto& frame=stack.back();
        if(c.ge(frame.point,end)){found=true;break;}
        if(!frame.prepared){frame.offers=candidates(frame.point);frame.prepared=true;}
        bool advanced=false;
        while(frame.pos<frame.offers.size()){
            Offer offer=frame.offers[frame.pos++];if(failed.count(offer.next))continue;
            path.push_back(offer);stack.push_back({offer.next,{},0,false});advanced=true;break;
        }
        if(!advanced){failed.insert(frame.point);stack.pop_back();if(!path.empty())path.pop_back();}
    }
    cout<<"{\"found\":"<<(found?"true":"false")<<",\"reused\":"<<reused<<",\"pruned\":"<<pruned<<",\"offers\":[";
    if(found)for(size_t i=0;i<path.size();++i){
        auto& o=path[i];if(i)cout<<',';cout<<"{\"move\":"<<o.move<<",\"lo\":"<<o.lo<<",\"hi\":"<<o.hi<<",\"keys\":[";
        for(size_t j=0;j<o.keys.size();++j){if(j)cout<<',';auto k=o.keys[j];cout<<'['<<k[0]<<','<<k[1]<<','<<k[2]<<']';}cout<<"]}";
    }
    cout<<"]}\n"<<flush;
    }
}
