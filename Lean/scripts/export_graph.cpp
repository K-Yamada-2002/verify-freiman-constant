// UNTRUSTED WITNESS EXPORTER: copied and instrumented from audit/independent_kernel.cpp.
// The Lean replay checker must validate every exported witness.
// Independent fixed-family verifier for the invariant partial-interval table.
//
// This file does not include or call the production verifier.  The .dat input
// is a mathematical certificate: its semantic connection to continued
// fractions must be checked separately.  Here all adopted rows are verified
// without deleting any of them.  No floating-point arithmetic is used.
//
// Endpoints have the form (1-t) F(u.lower) + t F(u.upper), on each side.
// Their differences are bounded by transport between positive and negative
// endpoint coefficients.  Both extreme 2-by-2 transports are evaluated and
// their rigorous bounds are intersected.  Connectivity is computed by a
// disjoint-set forest retaining every child vertex, augmented by certified
// common parent knots.  There is no bounded frontier or candidate truncation.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
#include <filesystem>
#include <queue>

namespace audit {
using Integer = std::int64_t;
using Wide = __int128_t;
constexpr Integer unit = Integer(1) << 48;

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}
Integer narrow(Wide n) {
    require(n >= std::numeric_limits<Integer>::min() &&
            n <= std::numeric_limits<Integer>::max(), "integer range exceeded");
    return static_cast<Integer>(n);
}
Integer floor_quotient(Wide n, Wide d) {
    require(d > 0, "nonpositive divisor");
    Wide q = n / d;
    if (n - q*d < 0) --q;
    return narrow(q);
}
Integer ceil_quotient(Wide n, Wide d) {
    require(d > 0, "nonpositive divisor");
    Wide q = n / d;
    if (n - q*d > 0) ++q;
    return narrow(q);
}
struct Range {
    Integer lower, upper;
};
Range sum(Range a, Range b) {
    return {narrow(Wide(a.lower)+b.lower), narrow(Wide(a.upper)+b.upper)};
}
Range negative(Range a) { return {narrow(-Wide(a.upper)), narrow(-Wide(a.lower))}; }
Range product(Range a, Range b) {
    const std::array<Wide,4> values = {
        Wide(a.lower)*b.lower, Wide(a.lower)*b.upper,
        Wide(a.upper)*b.lower, Wide(a.upper)*b.upper};
    const auto bounds = std::minmax_element(values.begin(), values.end());
    return {floor_quotient(*bounds.first,unit), ceil_quotient(*bounds.second,unit)};
}
Range quotient(Range a, Range b) {
    require(b.lower > 0, "divisor interval crosses zero");
    Integer lo=std::numeric_limits<Integer>::max();
    Integer hi=std::numeric_limits<Integer>::min();
    for (Integer x : {a.lower,a.upper}) for (Integer y : {b.lower,b.upper}) {
        lo=std::min(lo,floor_quotient(Wide(x)*unit,y));
        hi=std::max(hi,ceil_quotient(Wide(x)*unit,y));
    }
    return {lo,hi};
}

struct Transition {
    int state=-1, constant=0;
    bool spine=false;
    Range derivative{};
    std::array<int,2> endpoint{};
};
struct Side {
    int parity=0, anchor=0;
    Range shape{};
    std::vector<Range> tails, differences;
    std::vector<Transition> transitions;
    Range delta(int x, int y) const { return differences[x*tails.size()+y]; }
};
struct Pair { int left,right; bool spine; };
struct Input {
    int states=0, extensions=0, first=0, last=0, types=0, root=0;
    std::vector<Range> bands, grid;
    std::vector<Pair> pairs;
    std::vector<Side> sides;
    int bins() const { return last-first+1; }
};

Range read_range(std::istream& stream) {
    Range value{}; stream >> value.lower >> value.upper;
    require(bool(stream) && value.lower<=value.upper,"malformed interval");
    return value;
}
Input read_input(const std::string& name) {
    std::ifstream stream(name);
    require(bool(stream),"cannot open input");
    Input data; std::string magic; int pairs;
    stream >> magic >> data.states >> data.extensions >> data.first >> data.last
           >> data.types >> pairs >> data.root;
    require(bool(stream) && magic=="FREIMAN_DYADIC_GRAPH_V1","invalid input header");
    require(data.states>0 && data.extensions>0 && data.types>0 && pairs>0 &&
            data.last>=data.first,"invalid input dimensions");
    for(int t=0;t<data.types;++t) {
        Range b=read_range(stream);
        require(0<=b.lower && b.lower<b.upper && b.upper<=unit,"invalid band");
        data.bands.push_back(b);
    }
    for(int p=0;p<pairs;++p) {
        int a,b,flag; stream>>a>>b>>flag;
        require(bool(stream) && a>=0 && a<data.extensions && b>=0 &&
                b<data.extensions && (flag==0 || flag==1),"invalid successor pair");
        require(a!=0 || b!=0,"zero-length successor pair");
        data.pairs.push_back({a,b,flag==1});
    }
    for(int k=0;k<=data.bins();++k) data.grid.push_back(read_range(stream));
    require(data.grid.front().lower>0,"nonpositive ratio grid");
    for(int k=0;k<data.bins();++k)
        require(data.grid[k].upper < data.grid[k+1].lower,"grid boundaries unordered");
    for(int s=0;s<data.states;++s) {
        Range width=read_range(stream);
        require(width.lower>0,"nonpositive cylinder width");
        Side side; int count;
        stream>>side.parity;
        side.shape=read_range(stream);
        stream>>side.anchor>>count;
        require(bool(stream) && (side.parity==0 || side.parity==1) &&
                side.shape.lower>=0 && count>0 && side.anchor>=0 && side.anchor<count,
                "malformed side");
        for(int j=0;j<count;++j) side.tails.push_back(read_range(stream));
        for(int e=0;e<data.extensions;++e) {
            Transition transition;
            stream>>transition.state;
            require(bool(stream),"missing transition");
            if(transition.state>=0) {
                int flag; stream>>flag>>transition.constant;
                require(bool(stream) && transition.state<data.states &&
                        (flag==0 || flag==1) && transition.constant>=0,
                        "invalid transition fields");
                transition.spine=flag==1;
                transition.derivative=read_range(stream);
                require(transition.derivative.lower>0,"nonpositive derivative");
                (void)read_range(stream); (void)read_range(stream); // redundant eta data
                stream>>transition.endpoint[0]>>transition.endpoint[1];
                require(bool(stream),"missing transition endpoint");
                for(int index:transition.endpoint)
                    require(index>=0 && index<count,"invalid tail index");
            }
            side.transitions.push_back(transition);
        }
        require(side.transitions[0].state==s,"empty extension changes state");
        require(side.transitions[0].endpoint[0]==side.anchor,"empty lower endpoint mismatch");
        data.sides.push_back(std::move(side));
    }
    std::string extra; require(!(stream>>extra),"extra input token");
    return data;
}

// F(x)-F(y), divided by the magnitude of the parent's derivative at its
// lower-endpoint tail, equals sign*(x-y)*(1+r*anchor)^2/((1+r*x)*(1+r*y)).
// Each positive linear-fractional ratio is monotone in r; enclose its values
// at both shape endpoints. Identical arguments are cancelled symbolically.
void prepare_differences(Side& side) {
    const int count=static_cast<int>(side.tails.size());
    std::vector<Range> ratios;
    for(int i=0;i<count;++i) {
        if(i==side.anchor) { ratios.push_back({unit,unit}); continue; }
        Range bound{std::numeric_limits<Integer>::max(),std::numeric_limits<Integer>::min()};
        for(Integer r:{side.shape.lower,side.shape.upper}) {
            Range numerator=sum({unit,unit},product({r,r},side.tails[side.anchor]));
            Range denominator=sum({unit,unit},product({r,r},side.tails[i]));
            Range value=quotient(numerator,denominator);
            bound.lower=std::min(bound.lower,value.lower);
            bound.upper=std::max(bound.upper,value.upper);
        }
        ratios.push_back(bound);
    }
    side.differences.resize(count*count);
    for(int i=0;i<count;++i) for(int j=0;j<count;++j) {
        Range value{0,0};
        if(i!=j) {
            Range d=sum(side.tails[i],negative(side.tails[j]));
            value=product(d,product(ratios[i],ratios[j]));
            if(side.parity) value=negative(value);
        }
        side.differences[i*count+j]=value;
    }
}

struct Endpoint { int extension; Integer proportion; };
Range endpoint_difference(const Side& side,Endpoint left,Endpoint right) {
    std::array<int,4> id{};
    std::array<Integer,4> coefficient{};
    int used=0;
    auto append=[&](int index,Integer value) {
        for(int j=0;j<used;++j) if(id[j]==index) {coefficient[j]+=value;return;}
        id[used]=index; coefficient[used]=value; ++used;
    };
    const auto& a=side.transitions[left.extension].endpoint;
    const auto& b=side.transitions[right.extension].endpoint;
    append(a[0],unit-left.proportion); append(a[1],left.proportion);
    append(b[0],right.proportion-unit); append(b[1],-right.proportion);
    std::array<int,2> positive{},negative_ids{};
    std::array<Integer,2> supply{},demand{};
    int positives=0,negatives=0;
    for(int j=0;j<used;++j) {
        if(coefficient[j]>0) { positive[positives]=id[j]; supply[positives++]=coefficient[j]; }
        if(coefficient[j]<0) { negative_ids[negatives]=id[j]; demand[negatives++]=-coefficient[j]; }
    }
    if(!positives) { require(!negatives,"coefficient imbalance");return {0,0}; }
    require(positives<=2 && negatives<=2,"unexpected endpoint expression");
    Range result{std::numeric_limits<Integer>::min(),std::numeric_limits<Integer>::max()};
    for(int reverse=0;reverse<(negatives==2?2:1);++reverse) {
        auto remaining_supply=supply,remaining_demand=demand;
        Wide lower=0,upper=0;
        int i=0,j=0;
        while(i<positives && j<negatives) {
            int n=reverse?negatives-1-j:j;
            Integer amount=std::min(remaining_supply[i],remaining_demand[n]);
            Range d=side.delta(positive[i],negative_ids[n]);
            lower+=Wide(amount)*d.lower; upper+=Wide(amount)*d.upper;
            remaining_supply[i]-=amount;remaining_demand[n]-=amount;
            if(!remaining_supply[i])++i;
            if(!remaining_demand[n])++j;
        }
        require(i==positives && j==negatives,"unbalanced endpoint transport");
        result.lower=std::max(result.lower,floor_quotient(lower,unit));
        result.upper=std::min(result.upper,ceil_quotient(upper,unit));
    }
    require(result.lower<=result.upper,"inconsistent endpoint bounds");
    return result;
}

struct Vertex {
    int left_extension,right_extension;
    Integer lower,upper;
    int left_knot,right_knot;
    int pair_index, first_bin, last_bin;
    std::uint32_t type_mask;
};
struct Edge { int a,b,knot; };
struct Forest {
    std::vector<int> parent,size,left,right;
    explicit Forest(const std::vector<Vertex>& vertices) {
        const int n=static_cast<int>(vertices.size());
        parent.resize(n);std::iota(parent.begin(),parent.end(),0);
        size.assign(n,1);
        for(const auto& v:vertices) {left.push_back(v.left_knot);right.push_back(v.right_knot);}
    }
    int find(int i) { while(parent[i]!=i) {parent[i]=parent[parent[i]];i=parent[i];}return i; }
    bool join(int i,int j) {
        i=find(i);j=find(j);if(i==j)return false;
        if(size[i]<size[j])std::swap(i,j);
        parent[j]=i;size[i]+=size[j];left[i]=std::min(left[i],left[j]);right[i]=std::max(right[i],right[j]);
        return true;
    }
};

struct Counts {
    std::uint64_t cells=0,rows=0,vertices=0,endpoint_tests=0,pair_tests=0,unions=0;
};
struct Verifier {
    Input data;
    std::vector<unsigned char> alive;
    std::vector<int> unavailable_prefix;
    std::vector<Integer> knots;
    std::vector<std::pair<int,int>> band_knots;
    Counts counts;
    std::string export_folder;
    std::ofstream witness_stream;
    explicit Verifier(const std::string& input,const std::string& bits):data(read_input(input)) {
        for(auto& side:data.sides)prepare_differences(side);
        const std::size_t size=std::size_t(data.states)*data.states*data.bins()*data.types;
        std::ifstream binary(bits,std::ios::binary);require(bool(binary),"cannot open adopted table");
        alive.resize(size);
        binary.read(reinterpret_cast<char*>(alive.data()),static_cast<std::streamsize>(size));
        require(binary.gcount()==static_cast<std::streamsize>(size),"adopted table size mismatch");
        char extra;require(!binary.get(extra),"adopted table contains trailing bytes");
        for(auto value:alive)require(value==0 || value==1,"adopted table is not Boolean");
        require(std::count(alive.begin(),alive.end(),1)>0,"empty adopted table");
        unavailable_prefix.resize(std::size_t(data.states)*data.states*data.types*(data.bins()+1));
        for(int geometry=0;geometry<data.states*data.states;++geometry) for(int t=0;t<data.types;++t) {
            std::size_t start=(std::size_t(geometry)*data.types+t)*(data.bins()+1);
            for(int k=0;k<data.bins();++k)
                unavailable_prefix[start+k+1]=unavailable_prefix[start+k]+!alive[index(geometry,k,t)];
        }
        for(auto band:data.bands) {knots.push_back(band.lower);knots.push_back(band.upper);}
        std::sort(knots.begin(),knots.end());knots.erase(std::unique(knots.begin(),knots.end()),knots.end());
        for(auto band:data.bands)
            band_knots.push_back({std::lower_bound(knots.begin(),knots.end(),band.lower)-knots.begin(),
                                  std::lower_bound(knots.begin(),knots.end(),band.upper)-knots.begin()});
    }
    std::size_t index(int geometry,int k,int type) const {
        return (std::size_t(geometry)*data.bins()+k)*data.types+type;
    }
    bool available(int geometry,int first,int last,int type) const {
        require(first>=0 && first<=last && last<data.bins(),"empty or invalid destination-bin cover");
        std::size_t start=(std::size_t(geometry)*data.types+type)*(data.bins()+1);
        return unavailable_prefix[start+first]==unavailable_prefix[start+last+1];
    }
    bool mapped_bins(int parent,const Transition& left,const Transition& right,int& first,int& last) const {
        if(left.constant!=0 && left.constant==right.constant) {first=last=parent;return true;}
        Range factor=quotient(right.derivative,left.derivative);
        Range ratio{data.grid[parent].lower,data.grid[parent+1].upper};
        // Reject certainly unsuitable scales without constructing an overflowing
        // intermediate dyadic integer. Subsequent checks use outward bounds.
        if(Wide(ratio.lower)*factor.lower < Wide(unit)*data.grid.front().upper ||
           Wide(ratio.upper)*factor.upper > Wide(unit)*data.grid.back().lower)return false;
        Range image=product(ratio,factor);
        if(image.lower<data.grid.front().upper || image.upper>data.grid.back().lower)return false;
        // Pick a contiguous cover. Its outside endpoints lie beyond the entire
        // image even at the worst permitted positions of uncertain grid cuts.
        auto a=std::upper_bound(data.grid.begin(),data.grid.end(),image.lower,
                               [](Integer value,const Range& cut){return value<cut.upper;});
        auto b=std::lower_bound(data.grid.begin(),data.grid.end(),image.upper,
                               [](const Range& cut,Integer value){return cut.lower<value;});
        first=static_cast<int>(a-data.grid.begin())-1;
        last=static_cast<int>(b-data.grid.begin())-1;
        first=std::min(first,data.bins()-1);last=std::max(last,first);
        require(first>=0 && last<data.bins(),"destination image not covered by grid");
        require(data.grid[first].upper<=image.lower && image.upper<=data.grid[last+1].lower,
                "incorrect destination-bin enclosure");
        return true;
    }

    void write_u32(std::uint32_t x) {
        for(int i=0;i<4;++i) witness_stream.put(static_cast<char>((x>>(8*i))&255));
    }
    void write_u64(std::uint64_t x) {
        for(int i=0;i<8;++i) witness_stream.put(static_cast<char>((x>>(8*i))&255));
    }
    void export_cell(int geometry,int bin,const std::vector<Vertex>& vertices,
                     const std::vector<Edge>& edges, Forest& forest,
                     const std::vector<int>& adopted) {
        if(export_folder.empty())return;
        std::vector<std::vector<std::pair<int,int>>> adjacency(vertices.size());
        for(auto e:edges) {adjacency[e.a].push_back({e.b,e.knot});adjacency[e.b].push_back({e.a,e.knot});}
        struct Path {int type;std::vector<int> vertices,knots;};
        std::vector<Path> paths;
        std::vector<unsigned char> used(vertices.size(),0);
        for(int type:adopted) {
            int root=-1,start=-1,end=-1;
            for(int i=0;i<static_cast<int>(vertices.size());++i) if(forest.find(i)==i &&
                    forest.left[i]<=band_knots[type].first && forest.right[i]>=band_knots[type].second) {root=i;break;}
            require(root>=0,"export missing component");
            for(int i=0;i<static_cast<int>(vertices.size());++i) if(forest.find(i)==root) {
                if(start<0 && vertices[i].left_knot<=band_knots[type].first)start=i;
                if(end<0 && vertices[i].right_knot>=band_knots[type].second)end=i;
            }
            require(start>=0 && end>=0,"export missing boundary");
            std::vector<int> parent(vertices.size(),-1), link(vertices.size(),-2);
            std::queue<int> queue;queue.push(start);parent[start]=start;
            while(!queue.empty() && parent[end]<0) {
                int v=queue.front();queue.pop();
                for(auto edge:adjacency[v])if(parent[edge.first]<0) {
                    parent[edge.first]=v;link[edge.first]=edge.second;queue.push(edge.first);
                }
            }
            require(parent[end]>=0,"export disconnected forest");
            Path path;path.type=type;
            for(int v=end;;v=parent[v]) {path.vertices.push_back(v);used[v]=1;if(v==start)break;path.knots.push_back(link[v]);}
            std::reverse(path.vertices.begin(),path.vertices.end());
            std::reverse(path.knots.begin(),path.knots.end());paths.push_back(std::move(path));
        }
        std::vector<int> compact(vertices.size(),-1);int count=0;
        for(int i=0;i<static_cast<int>(vertices.size());++i)if(used[i])compact[i]=count++;
        write_u32(bin);write_u32(count);
        for(int i=0;i<static_cast<int>(vertices.size());++i)if(used[i]) {
            const auto& v=vertices[i];
            write_u32(v.pair_index);write_u64(v.lower);write_u64(v.upper);
            write_u32(v.first_bin);write_u32(v.last_bin);write_u32(v.type_mask);
            write_u32(v.left_knot);write_u32(v.right_knot+1);
        }
        write_u32(paths.size());
        for(const auto& path:paths) {
            write_u32(path.type);write_u32(path.vertices.size());
            for(int v:path.vertices)write_u32(compact[v]);
            for(int knot:path.knots)write_u32(knot+1);
        }
        require(bool(witness_stream),"export write failure");
    }

    bool verify_cell(int geometry,int k,std::ostream& errors) {
        std::vector<int> adopted;
        for(int t=0;t<data.types;++t)if(alive[index(geometry,k,t)])adopted.push_back(t);
        if(adopted.empty())return true;
        ++counts.cells;counts.rows+=adopted.size();
        const auto& left=data.sides[geometry/data.states];
        const auto& right=data.sides[geometry%data.states];
        Range ratio{data.grid[k].lower,data.grid[k+1].upper};
        auto greater_equal=[&](int au,int av,Integer at,int bu,int bv,Integer bt) {
            ++counts.endpoint_tests;
            Range a=endpoint_difference(left,{au,at},{bu,bt});
            Range b=endpoint_difference(right,{av,at},{bv,bt});
            Wide lower=Wide(a.lower)*unit+std::min(Wide(ratio.lower)*b.lower,Wide(ratio.upper)*b.lower);
            return lower>=0;
        };
        std::vector<Vertex> vertices;
        for(int pair_index=0;pair_index<static_cast<int>(data.pairs.size());++pair_index) {
            auto pair=data.pairs[pair_index];
            const auto& x=left.transitions[pair.left];
            const auto& y=right.transitions[pair.right];
            if(x.state<0 || y.state<0 || (pair.spine && (!x.spine || !y.spine)))continue;
            int first,last;
            if(!mapped_bins(k,x,y,first,last))continue;
            std::vector<Range> permitted;
            for(int type=0;type<data.types;++type)
                if(available(x.state*data.states+y.state,first,last,type))permitted.push_back(data.bands[type]);
            std::sort(permitted.begin(),permitted.end(),[](Range a,Range b){return a.lower<b.lower;});
            std::vector<Range> merged;
            for(Range band:permitted) {
                if(!merged.empty() && band.lower<=merged.back().upper)
                    merged.back().upper=std::max(merged.back().upper,band.upper);
                else merged.push_back(band);
            }
            for(Range band:merged) {
                // Find two explicitly certified anchor knots. Binary search is
                // only a search heuristic: stored indices always had a true
                // inequality, and later knots are ordered mathematically.
                int lower=static_cast<int>(knots.size()),upper=-1;
                int a=0,b=static_cast<int>(knots.size());
                while(a<b) {
                    int mid=a+(b-a)/2;
                    if(greater_equal(0,0,knots[mid],pair.left,pair.right,band.lower)) {lower=mid;b=mid;}
                    else a=mid+1;
                }
                a=0;b=static_cast<int>(knots.size());
                while(a<b) {
                    int mid=a+(b-a)/2;
                    if(greater_equal(pair.left,pair.right,band.upper,0,0,knots[mid])) {upper=mid;a=mid+1;}
                    else b=mid;
                }
                std::uint32_t mask=0;
                for(int t=0;t<data.types;++t) if(available(x.state*data.states+y.state,first,last,t) &&
                        band.lower<=data.bands[t].lower && data.bands[t].upper<=band.upper) mask|=std::uint32_t(1)<<t;
                vertices.push_back({pair.left,pair.right,band.lower,band.upper,lower,upper,pair_index,first,last,mask});
            }
        }
        counts.vertices+=vertices.size();
        Forest forest(vertices);
        std::vector<Edge> edges;
        auto covered=[&]() {
            for(int type:adopted) {
                bool ok=false;
                for(int i=0;i<static_cast<int>(vertices.size());++i)if(forest.find(i)==i &&
                   forest.left[i]<=band_knots[type].first && forest.right[i]>=band_knots[type].second) {ok=true;break;}
                if(!ok)return false;
            }
            return true;
        };
        // A shared parent knot is an independently certified intersection.
        // This often finds a spanning forest before any pair comparison.
        std::vector<int> owner(knots.size(),-1);
        for(int i=0;i<static_cast<int>(vertices.size());++i) {
            for(int knot=vertices[i].left_knot;knot<=vertices[i].right_knot;++knot) {
                if(owner[knot]<0)owner[knot]=i;
                else if(forest.join(i,owner[knot])) {++counts.unions;edges.push_back({i,owner[knot],knot});}
            }
        }
        if(covered()) {export_cell(geometry,k,vertices,edges,forest,adopted);return true;}
        // Retain all vertices. Examine every as-yet-disconnected pair until
        // there is a complete proof, or all candidate edges are exhausted.
        for(int i=0;i<static_cast<int>(vertices.size());++i) {
            const auto& v=vertices[i];
            for(int j=0;j<i;++j) {
                if(forest.find(i)==forest.find(j))continue;
                ++counts.pair_tests;
                const auto& w=vertices[j];
                if(greater_equal(v.left_extension,v.right_extension,v.upper,
                                 w.left_extension,w.right_extension,w.lower) &&
                   greater_equal(w.left_extension,w.right_extension,w.upper,
                                 v.left_extension,v.right_extension,v.lower)) {
                    forest.join(i,j);++counts.unions;edges.push_back({i,j,-1});
                    if(covered()) {export_cell(geometry,k,vertices,edges,forest,adopted);return true;}
                }
            }
        }
        errors<<"uncovered adopted row(s): geometry="<<geometry<<" bin="<<k+data.first<<" types=";
        for(int type:adopted) {
            bool ok=false;
            for(int i=0;i<static_cast<int>(vertices.size());++i)if(forest.find(i)==i &&
               forest.left[i]<=band_knots[type].first && forest.right[i]>=band_knots[type].second)ok=true;
            if(!ok)errors<<type<<',';
        }
        errors<<" vertices="<<vertices.size()<<'\n';
        return false;
    }
    bool run(int begin,int end) {
        require(begin>=0 && end<=data.states*data.states && begin<end,"invalid geometry range");
        auto start=std::chrono::steady_clock::now();
        std::uint64_t failures=0;
        for(int geometry=begin;geometry<end;++geometry) {
            if(!export_folder.empty()) {
                std::filesystem::create_directories(export_folder);
                witness_stream.open(export_folder+"/geometry_"+std::to_string(geometry)+".bin",std::ios::binary);
                require(bool(witness_stream),"cannot open export witness");
                write_u32(0x3143474c);write_u32(geometry);
            }
            for(int bin=0;bin<data.bins();++bin)
                if(!verify_cell(geometry,bin,std::cerr))++failures;
            if(!export_folder.empty()){write_u32(0xffffffff);witness_stream.close();}
            if((geometry-begin+1)%11==0 || geometry+1==end) {
                std::cout<<"{\"geometry_finished\":"<<geometry<<",\"rows\":"<<counts.rows
                         <<",\"vertices\":"<<counts.vertices<<",\"pair_tests\":"<<counts.pair_tests
                         <<",\"failures\":"<<failures<<",\"seconds\":"
                         <<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n"<<std::flush;
            }
        }
        std::cout<<"{\"passed\":"<<(failures?"false":"true")
                 <<",\"geometry_range\":["<<begin<<','<<end<<"],\"adopted_rows\":"<<counts.rows
                 <<",\"adopted_cells\":"<<counts.cells<<",\"child_vertices\":"<<counts.vertices
                 <<",\"endpoint_tests\":"<<counts.endpoint_tests<<",\"pair_tests\":"<<counts.pair_tests
                 <<",\"certified_unions\":"<<counts.unions<<",\"failed_cells\":"<<failures<<"}\n";
        return failures==0;
    }
};
} // namespace audit

int main(int argc,char** argv) {
    try {
        audit::require(argc==4 || argc==6,"usage: export_graph input.dat alive.bin export_folder [geometry_begin geometry_end]");
        audit::Verifier verifier(argv[1],argv[2]);
        verifier.export_folder=argv[3];
        int first=argc==6?std::stoi(argv[4]):0;
        int last=argc==6?std::stoi(argv[5]):verifier.data.states*verifier.data.states;
        return verifier.run(first,last)?0:1;
    } catch(const std::exception& e) {
        std::cerr<<"verification error: "<<e.what()<<'\n';return 2;
    }
}
