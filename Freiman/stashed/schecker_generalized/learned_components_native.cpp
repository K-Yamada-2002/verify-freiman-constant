// Optional accelerator for floating component discovery. No proof assertions.
// Geometry, legal moves, and dependency maps are exported by the Python driver.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

struct Point { double x,y; bool operator==(const Point& b) const {return x==b.x && y==b.y;} };
using Interval=std::pair<int,int>;
using Mask=std::vector<uint64_t>;
struct Move { int pool; std::vector<std::pair<int,int>> dependencies; };
struct Cell {
    int pool,mode,p;
    double rl,rh,sl,sh,ql,qh,alpha,beta;
    std::vector<int> order;
    std::vector<Interval> domain;
    std::vector<Move> moves;

    static std::pair<double,double> delta(double l,double h,double z,double x,double y) {
        if(x==y) return {0.,0.};
        // The derivative factors as (1+z*r) times a linear polynomial.
        // For extremal anchors the remaining root is outside the r box;
        // retaining the general root also handles floating rounding near
        // coincident endpoint values without square roots or allocations.
        double slope=z*(x+y)-2*x*y;
        double points[3]={l,h,0.};int count=2;
        if(slope!=0.) {
            double root=(x+y-2*z)/slope;
            if(l<root && root<h) points[count++]=root;
        }
        double low=INFINITY,high=-INFINITY;
        for(int i=0;i<count;++i) {
            double r=points[i];
            double v=(x-y)*(1+z*r)*(1+z*r)/((1+r*x)*(1+r*y));
            low=std::min(low,v);high=std::max(high,v);
        }
        return {low,high};
    }
    bool ge(Point a,Point b) const {
        if(a==b) return true;
        if(mode) {
            double dl=delta(rl,rh,alpha,a.x,b.x).first;
            auto rr=delta(sl,sh,beta,a.y,b.y);
            double dr=p>0 ? rr.first : -rr.second;
            return dl+(dr>=0 ? ql:qh)*dr>=-1e-12;
        }
        double dr=a.x-b.x,ds=p*(a.y-b.y);
        double r=dr>=0 ? rh:rl,s=ds>=0 ? sh:sl,q=ds>=0 ? ql:qh;
        return dr/((1+r*a.x)*(1+r*b.x))+q*ds/((1+s*a.y)*(1+s*b.y))>=-1e-13;
    }
    double value(Point a) const {
        double r=(rl+rh)/2,s=(sl+sh)/2,q=(ql+qh)/2;
        if(mode) return (1+r*alpha)*(1+r*alpha)*a.x/(1+r*a.x)
            +p*q*(1+s*beta)*(1+s*beta)*a.y/(1+s*a.y);
        return a.x/(1+r*a.x)+p*q*a.y/(1+s*a.y);
    }
};
struct Offer { double low,high; Point a,b; };
struct History { int round,cells,components,changed; };
struct Group { int count=0,first=0,last=0;double low=0.,high=0.; };

int main(int argc,char** argv) {
    if(argc!=4) {std::cerr<<"input output rounds required\n";return 2;}
    std::ifstream in(argv[1]);int np,nm,nc;
    in>>np>>nm>>nc;
    std::vector<std::vector<Point>> pools(np);
    std::vector<std::vector<int>> maps(nm);
    for(auto& pool:pools) {int n;in>>n;pool.resize(n);for(auto& z:pool) in>>z.x>>z.y;}
    for(auto& map:maps) {int n;in>>n;map.resize(n);for(int& z:map) in>>z;}
    std::vector<Cell> cells(nc);
    for(auto& c:cells) {
        in>>c.pool>>c.mode>>c.p>>c.rl>>c.rh>>c.sl>>c.sh>>c.ql>>c.qh>>c.alpha>>c.beta;
        int n;in>>n;c.domain.resize(n);for(auto& d:c.domain) in>>d.first>>d.second;
        in>>n;c.order.resize(n);for(int& i:c.order) in>>i;
        in>>n;c.moves.resize(n);
        for(auto& m:c.moves) {
            int count;in>>m.pool>>count;m.dependencies.resize(count);
            for(auto& d:m.dependencies) in>>d.first>>d.second;
        }
    }
    if(!in) {std::cerr<<"incomplete input\n";return 2;}
    std::vector<History> history;
    for(int round=0;round<std::stoi(argv[3]);++round) {
        std::vector<std::vector<int>> memberships(nc);
        std::vector<std::vector<Mask>> old_masks(nc);
        for(int cid=0;cid<nc;++cid) {
            auto& c=cells[cid];auto& points=pools[c.pool];auto& member=memberships[cid];
            member.assign(points.size(),-1);
            int size=points.size(),words=(size+63)/64;
            if(c.domain.empty()) continue;
            // Reuse comparisons with old boundaries across all interval
            // intersections. This is the same component update as Python.
            std::vector<int8_t> comparisons(size*size,-1);
            auto compare=[&](int a,int b) {
                auto& value=comparisons[a*size+b];
                if(value<0) value=c.ge(points[a],points[b]) ? 1:0;
                return value!=0;
            };
            for(int j=0;j<(int)c.domain.size();++j) {
                auto [a,b]=c.domain[j];Mask mask(words,0);
                for(int rank=0;rank<size;++rank) {
                    int i=c.order[rank];
                    if(compare(i,a) && compare(b,i)) {
                        mask[rank/64]|=uint64_t(1)<<(rank%64);
                        if(member[i]<0) member[i]=j;
                    }
                }
                old_masks[cid].push_back(std::move(mask));
            }
        }
        std::vector<std::vector<Interval>> revised(nc);
        for(int cid=0;cid<nc;++cid) {
            auto& c=cells[cid];if(c.domain.empty()) continue;
            auto& points=pools[c.pool];std::vector<Offer> offers;
            for(auto& m:c.moves) {
                auto& mapped=pools[m.pool];std::map<std::vector<int>,Group> groups;
                std::vector<int> key(m.dependencies.size());
                for(int i=0;i<(int)mapped.size();++i) {
                    bool valid=true;int position=0;
                    for(auto [d,ids]:m.dependencies) {
                        int k=memberships[d][maps[ids][i]];
                        if(k<0) {valid=false;break;}key[position++]=k;
                    }
                    if(valid) {
                        auto& group=groups[key];double value=c.value(mapped[i]);
                        if(!group.count || value<group.low) {group.low=value;group.first=i;}
                        // Stable sorting picks the last index among tied
                        // maxima, and the first index among tied minima.
                        if(!group.count || value>=group.high) {group.high=value;group.last=i;}
                        ++group.count;
                    }
                }
                for(auto& group:groups) {
                    auto& g=group.second;if(g.count<2) continue;
                    Point a=mapped[g.first],b=mapped[g.last];
                    if(c.ge(b,a)) offers.push_back({g.low,g.high,a,b});
                }
            }
            std::sort(offers.begin(),offers.end(),[](const Offer& a,const Offer& b){
                return std::tie(a.low,a.high,a.a.x,a.a.y,a.b.x,a.b.y)
                     < std::tie(b.low,b.high,b.a.x,b.a.y,b.b.x,b.b.y);
            });
            std::vector<std::pair<Point,Point>> merged;
            for(auto& o:offers) {
                if(!merged.empty() && c.ge(merged.back().second,o.a)) {
                    if(c.ge(o.b,merged.back().second)) merged.back().second=o.b;
                } else merged.push_back({o.a,o.b});
            }
            int size=points.size(),words=(size+63)/64;
            std::vector<Mask> new_masks;
            std::vector<uint8_t> emitted(size*size,0);
            for(auto [lo,hi]:merged) {
                Mask mask(words,0);
                for(int rank=0;rank<size;++rank) {
                    int i=c.order[rank];
                    if(c.ge(points[i],lo) && c.ge(hi,points[i])) {
                        mask[rank/64]|=uint64_t(1)<<(rank%64);
                    }
                }
                new_masks.push_back(std::move(mask));
            }
            for(auto& old:old_masks[cid]) for(auto& fresh:new_masks) {
                int first=-1,last=-1;
                for(int word=0;word<words;++word) {
                    uint64_t common=old[word]&fresh[word];
                    if(!common) continue;
                    if(first<0) first=64*word+__builtin_ctzll(common);
                    last=64*word+63-__builtin_clzll(common);
                }
                if(first>=0 && first!=last) {
                    int a=c.order[first],b=c.order[last];
                    if(!emitted[a*size+b] && c.ge(points[b],points[a])) {
                        emitted[a*size+b]=1;revised[cid].push_back({a,b});
                    }
                }
            }
        }
        History row{round,0,0,0};
        for(int cid=0;cid<nc;++cid) {
            if(revised[cid]!=cells[cid].domain) ++row.changed;
            cells[cid].domain=std::move(revised[cid]);
            if(!cells[cid].domain.empty()) ++row.cells;
            row.components+=cells[cid].domain.size();
        }
        history.push_back(row);
        std::cout<<"{\"round\":"<<round<<",\"nonempty_cells\":"<<row.cells
                 <<",\"components\":"<<row.components<<",\"changed\":"<<row.changed<<"}"<<std::endl;
        if(!row.changed) break;
    }
    std::ofstream out(argv[2]);out<<"{\"history\":[";
    for(int i=0;i<(int)history.size();++i) {
        if(i) out<<',';auto h=history[i];
        out<<"{\"round\":"<<h.round<<",\"nonempty_cells\":"<<h.cells
           <<",\"components\":"<<h.components<<",\"changed\":"<<h.changed<<"}";
    }
    out<<"],\"domains\":[";bool first=true;
    for(int cid=0;cid<nc;++cid) if(!cells[cid].domain.empty()) {
        if(!first) out<<',';first=false;out<<"{\"cell\":"<<cid<<",\"intervals\":[";
        for(int i=0;i<(int)cells[cid].domain.size();++i) {
            if(i) out<<',';auto d=cells[cid].domain[i];out<<'['<<d.first<<','<<d.second<<']';
        }
        out<<"]}";
    }
    out<<"]}\n";
}
