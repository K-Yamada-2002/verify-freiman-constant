// Certified finite-scale coverage, NOT a proof of an interval in K_F + K_F.
// Build: c++ -O3 -std=c++17 numerical_cover.cpp -o /tmp/kf131-cover
// Run: /tmp/kf131-cover 10    (sum-cylinder width <= 10^-10)
// All decisions use integer arithmetic. No floating-point tolerance is used.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

using I = __int128_t;
using U = __uint128_t;
using T = std::int64_t;
constexpr T SCALE = 1000000000000000LL;
constexpr T SQRT_LO = 3162277660168379LL;
constexpr T SQRT_HI = SQRT_LO + 1;
constexpr T TARGET_LO = 1292880000000000LL;
constexpr T TARGET_HI = 1292906000000000LL;
const I MAX_I = static_cast<I>((~U(0)) >> 1);

struct Rational { I n, d; };
struct Cylinder {
    T a=1, b=0, c=0, d=1;
    int state=0, depth=0;
    T outer_lo=0, inner_lo=0, inner_hi=0, outer_hi=0;
};

int next_state(int s, int digit) {
    if (s == 2 && digit == 1) return -1;
    if (digit == 1) return 1;
    if (s == 1 && digit == 3) return 2;
    return 0;
}

Rational tail(int state, bool high, T radical) {
    if (high) {
        if (state == 2) return {2*I(radical)-5*I(SCALE), 3*I(SCALE)};
        return {2*I(radical)-4*I(SCALE), 3*I(SCALE)};
    }
    if (state == 1) return {I(radical)-2*I(SCALE), 4*I(SCALE)};
    return {2*I(radical)-5*I(SCALE), 5*I(SCALE)};
}

T endpoint(const Cylinder& z, Rational t, bool round_up) {
    I numerator = I(z.a)*t.n + I(z.b)*t.d;
    I denominator = I(z.c)*t.n + I(z.d)*t.d;
    if (numerator <= 0 || denominator <= 0 || numerator > MAX_I/SCALE)
        throw std::runtime_error("Rational arithmetic range exceeded");
    I scaled = numerator*SCALE;
    I result = scaled/denominator + (round_up && scaled%denominator != 0);
    if (result > std::numeric_limits<T>::max())
        throw std::runtime_error("Endpoint range exceeded");
    return T(result);
}

Cylinder bounds(Cylinder z) {
    bool odd = z.depth%2;
    // In odd depth phi is decreasing; reverse the radical bracket as well.
    z.outer_lo = endpoint(z, tail(z.state, odd, odd ? SQRT_HI : SQRT_LO), false);
    z.inner_lo = endpoint(z, tail(z.state, odd, odd ? SQRT_LO : SQRT_HI), true);
    z.inner_hi = endpoint(z, tail(z.state, !odd, odd ? SQRT_HI : SQRT_LO), false);
    z.outer_hi = endpoint(z, tail(z.state, !odd, odd ? SQRT_LO : SQRT_HI), true);
    return z;
}

Cylinder child(const Cylinder& z, int digit) {
    int s = next_state(z.state, digit);
    if (s < 0) throw std::runtime_error("Forbidden word");
    I b=I(z.a)+digit*I(z.b), d=I(z.c)+digit*I(z.d);
    if (b > std::numeric_limits<T>::max() || d > std::numeric_limits<T>::max())
        throw std::runtime_error("Matrix range exceeded");
    Cylinder result;
    result.a=z.b; result.b=T(b); result.c=z.d; result.d=T(d);
    result.state=s; result.depth=z.depth+1;
    return bounds(result);
}

Cylinder prefix(const std::string& word) {
    Cylinder z = bounds(Cylinder{});
    for (char digit : word) {
        if (digit < '1' || digit > '3') throw std::runtime_error("Invalid digit");
        z=child(z, digit-'0');
    }
    return z;
}

struct Cover {
    std::map<T,T> components;
    bool contains(T lo, T hi) const {
        auto it = components.upper_bound(lo);
        return it != components.begin() && std::prev(it)->second >= hi;
    }
    void insert(T lo, T hi) {
        if (lo > hi) return;
        auto it = components.lower_bound(lo);
        if (it != components.begin() && std::prev(it)->second >= lo) --it;
        while (it != components.end() && it->first <= hi) {
            lo=std::min(lo,it->first); hi=std::max(hi,it->second);
            it=components.erase(it);
        }
        components.emplace(lo,hi);
    }
};

int main(int argc, char** argv) try {
    // Exact rational radical enclosure, checked before every run.
    if (!(I(SQRT_LO)*SQRT_LO < 10*I(SCALE)*SCALE &&
          I(SQRT_HI)*SQRT_HI > 10*I(SCALE)*SCALE))
        throw std::runtime_error("Invalid radical enclosure");
    if (argc >= 2 && std::string(argv[1]) == "--cylinders") {
        std::cout << "[";
        for (int k=2;k<argc;++k) {
            Cylinder z=prefix(argv[k]);
            if (k>2) std::cout << ",";
            std::cout << "{\"word\":\"" << argv[k] << "\",\"bounds\":["
                      << z.outer_lo << "," << z.inner_lo << ","
                      << z.inner_hi << "," << z.outer_hi << "]}";
        }
        std::cout << "]\n";
        return 0;
    }
    int exponent=argc>=2 ? std::stoi(argv[1]) : 9;
    std::uint64_t budget=argc>=3 ? std::stoull(argv[2]) : 200000000;
    bool prune=argc<4 || std::string(argv[3])!="--no-prune";
    if (exponent<1 || exponent>13) throw std::runtime_error("Exponent must be 1..13");
    T epsilon=SCALE;
    for (int k=0;k<exponent;++k) epsilon/=10;
    auto start=std::chrono::steady_clock::now();
    std::vector<std::pair<Cylinder,Cylinder>> stack{{prefix("112"),prefix("122")}};
    Cover cover;
    std::uint64_t visited=0, leaves=0, redundant=0, disjoint=0;
    int max_depth=0;
    bool exhausted=false;
    while (!stack.empty()) {
        if (visited>=budget) { exhausted=true; break; }
        auto pair=stack.back(); stack.pop_back(); ++visited;
        Cylinder u=pair.first, v=pair.second;
        T lo=u.outer_lo+v.outer_lo, hi=u.outer_hi+v.outer_hi;
        if (hi<TARGET_LO || lo>TARGET_HI) { ++disjoint; continue; }
        if (prune && cover.contains(std::max(lo,TARGET_LO),std::min(hi,TARGET_HI))) {
            ++redundant; continue;
        }
        if (hi-lo<=epsilon) {
            ++leaves;
            max_depth=std::max({max_depth,u.depth,v.depth});
            cover.insert(std::max(TARGET_LO,u.inner_lo+v.inner_lo),
                         std::min(TARGET_HI,u.inner_hi+v.inner_hi));
            continue;
        }
        bool split_left=u.outer_hi-u.outer_lo>=v.outer_hi-v.outer_lo;
        const Cylinder& z=split_left ? u : v;
        for (int digit=3;digit>=1;--digit) {
            if (next_state(z.state,digit)<0) continue;
            Cylinder w=child(z,digit);
            stack.emplace_back(split_left ? w : u, split_left ? v : w);
        }
    }
    T length=0, max_gap=0, frontier=TARGET_LO;
    std::size_t gaps=0;
    for (auto interval : cover.components) {
        if (interval.first>frontier) { ++gaps; max_gap=std::max(max_gap,interval.first-frontier); }
        frontier=std::max(frontier,interval.second);
        length+=interval.second-interval.first;
    }
    if (frontier<TARGET_HI) { ++gaps; max_gap=std::max(max_gap,TARGET_HI-frontier); }
    double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "{\"exponent\":" << exponent << ",\"epsilon\":\"1e-" << exponent
              << "\",\"integer_scale\":" << SCALE << ",\"visited\":" << visited
              << ",\"accepted_sum_hulls\":" << leaves << ",\"redundant_subtrees\":" << redundant
              << ",\"disjoint_subtrees\":" << disjoint << ",\"max_prefix_length\":" << max_depth
              << ",\"components\":" << cover.components.size() << ",\"uncovered_components\":" << gaps
              << ",\"max_uncovered_grid_units\":" << max_gap << ",\"covered_grid_units\":" << length
              << ",\"covers_target_at_this_finite_scale_only\":"
              << (cover.contains(TARGET_LO,TARGET_HI) ? "true" : "false")
              << ",\"budget_exhausted\":" << (exhausted ? "true" : "false")
              << ",\"pruning\":" << (prune ? "true" : "false")
              << ",\"elapsed_seconds\":" << std::setprecision(6) << elapsed << "}\n";
    return 0;
} catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 1;
}
