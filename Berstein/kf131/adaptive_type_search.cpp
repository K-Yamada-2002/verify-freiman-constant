// Floating discovery for automatically growing interval types.
// Exact validation: verify_type_graph.py. Open nodes are proof obligations.
// Usage: engine MENU MEMORY BINS BASE MAX_STEP ROUNDS OUTPUT_JSON
//
// A child gets only the interval used by its parent. Its endpoint type is
// added on demand; overlapping requests in the same parameter cell merge.
// Enlarging a type schedules its cover for recomputation. Only nodes reached
// from the current root are exported. No finite frontier is treated as filled.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
using namespace std;
struct Pt {
  double x, y;
};
// Tail coordinates depend only on the two automaton states, not on the
// parameter box. Share their immutable table instead of copying it in every
// cell; large endpoint menus otherwise consume several gigabytes needlessly.
struct PointPool {
  shared_ptr<const vector<Pt>> points;
  size_t size() const { return points->size(); }
  const Pt &operator[](size_t i) const { return (*points)[i]; }
};
struct Bounds {
  double lo, hi;
};
struct Shape {
  string word;
  int state;
  Bounds r;
};
struct Dep {
  int cell;
  bool swap;
  Bounds required_ratio{0, 1};
};
struct Move {
  string u, v;
  int sl, sr;
  vector<Dep> deps;
  shared_ptr<vector<Pt>> mapped;
};
using Bits = vector<uint64_t>;
struct Cell {
  map<tuple<double, double, bool>, Bits> bound_cache;
  int s, t, p, qi;
  Bounds r, sb, q;
  PointPool pool;
  vector<int> order;
  vector<Move> moves;
  vector<pair<int, int>> dom;
};
vector<Shape> shapes;
vector<vector<double>> sides(3);
vector<vector<pair<string, int>>> labels(3);
// Stable references also permit the lazy engine to add arrival cells while
// constructing a parent's moves.
deque<Cell> cells;
map<pair<int, int>, shared_ptr<const vector<Pt>>> shared_pools;
unordered_map<string, int> shape_lookup;
int longest_shape = 0;
int minimum_shape_memory = 0;
map<tuple<int, int, string, string>, shared_ptr<vector<Pt>>> mapped_cache;
const double anchor = sqrt(2.0) - 1;
string root_left, root_right;
int bins = 24, memory = 2, menu = 1, maxstep = 2, work_budget = 100000;
double base = .88;
string pool_mode = "extrema";
int grid_power = 4;
vector<Bounds> qb;
#include "ratio_refinement.hpp"
int state(string w) {
  int k = 0;
  for (char c : w) {
    if (k == 2 && c == '1')
      return -1;
    if (c == '1')
      k = 1;
    else if (k == 1 && c == '3')
      k = 2;
    else
      k = 0;
  }
  return k;
}
vector<string> words(int s, int n) {
  vector<string> v = {""};
  while (n--) {
    vector<string> a;
    for (auto w : v)
      for (char c : string("123")) {
        string z = (s == 1 ? "1" : s == 2 ? "13" : "") + w + c;
        if (state(z) >= 0)
          a.push_back(w + c);
      }
    v = a;
  }
  return v;
}
array<double, 4> mat(string w) {
  double a = 1, b = 0, c = 0, d = 1;
  for (char x : w) {
    double k = x - '0';
    double aa = b, bb = a + k * b, cc = d, dd = c + k * d;
    a = aa;
    b = bb;
    c = cc;
    d = dd;
  }
  return {a, b, c, d};
}
double phi(string w, double x) {
  auto m = mat(w);
  return (m[0] * x + m[1]) / (m[2] * x + m[3]);
}
int dst(int s, string w) {
  string z = shapes[s].word + w;
  if (state(z) < 0)
    return -1;
  for (int n = min(longest_shape, int(z.size())); n > 0; --n) {
    auto found = shape_lookup.find(z.substr(z.size() - n));
    if (found != shape_lookup.end())
      return found->second;
  }
  return -1;
}
int id(int s, int t, int p, int qi) {
  return (((s * shapes.size() + t) * 2 + (p < 0)) * bins) + qi;
}
double val(const Cell &c, Pt z) {
  double r = (c.r.lo + c.r.hi) / 2, s = (c.sb.lo + c.sb.hi) / 2,
         q = (c.q.lo + c.q.hi) / 2;
  return pow(1 + r * anchor, 2) * z.x / (1 + r * z.x) +
         c.p * q * pow(1 + s * anchor, 2) * z.y / (1 + s * z.y);
}
double delta_min(double x, double y, Bounds rb) {
  auto f = [&](double r) {
    return (x - y) * pow(1 + r * anchor, 2) / ((1 + r * x) * (1 + r * y));
  };
  double low = min(f(rb.lo), f(rb.hi)), den = anchor * (x + y) - 2 * x * y;
  if (abs(den) > 1e-18) {
    double z = -(2 * anchor - x - y) / den;
    if (rb.lo < z && z < rb.hi)
      low = min(low, f(z));
  }
  return low;
}
bool ge(const Cell &c, Pt a, Pt b) {
  if (a.x == b.x && a.y == b.y)
    return true;
  double dx = delta_min(a.x, b.x, c.r),
         dy = c.p > 0 ? delta_min(a.y, b.y, c.sb) : delta_min(b.y, a.y, c.sb);
  return dx + (dy >= 0 ? c.q.lo : c.q.hi) * dy >= -1e-13;
}
vector<Pt> pool(int s, int t) {
  vector<Pt> out;
  for (double x : sides[s])
    for (double y : sides[t])
      out.push_back({x, y});
  return out;
}
void prepare_catalog() {
  double a = (2 * sqrt(10) - 5) / 5, b = (2 * sqrt(10) - 4) / 3,
         c = (sqrt(10) - 2) / 4, d = (2 * sqrt(10) - 5) / 3;
  array<Bounds, 3> tails = {Bounds{a, b}, Bounds{c, b}, Bounds{a, d}};
  if (pool_mode == "grid" || pool_mode == "mixed") {
    int divisions = 1 << grid_power;
    for (int s = 0; s < 3; s++)
      for (int i = 0; i <= divisions; i++) {
        labels[s].push_back(
            {"@" + to_string(i) + "/" + to_string(divisions), 0});
        sides[s].push_back(tails[s].lo +
                           (tails[s].hi - tails[s].lo) * i / divisions);
      }
  }
  if (pool_mode != "grid")
    for (int s = 0; s < 3; s++)
      for (auto w : words(s, menu)) {
        int t = state((s == 1 ? "1" : s == 2 ? "13" : "") + w);
        for (int h = 0; h < 2; h++) {
          labels[s].push_back({w, h});
          sides[s].push_back(phi(w, h ? tails[t].hi : tails[t].lo));
        }
      }
  if (pool_mode == "periodic" || pool_mode == "centered")
    for (int s = 0; s < 3; ++s) {
      for (auto w : words(s, menu)) {
        labels[s].push_back({w + "~2", 0});
        sides[s].push_back(phi(w, anchor));
      }
      if (pool_mode == "centered")
        for (int k = 3; k <= grid_power; ++k)
          for (int sign : {-1, 1}) {
            double x = anchor + sign * ldexp(1., -k);
            if (x < tails[s].lo || x > tails[s].hi)
              continue;
            labels[s].push_back(
                {"#" + to_string(sign) + "/" + to_string(1 << k), 0});
            sides[s].push_back(x);
          }
    }
  vector<string> st = words(0, memory);
  if (minimum_shape_memory > 0)
    for (int n = minimum_shape_memory; n < memory; ++n) {
      auto shorter = words(0, n);
      st.insert(st.end(), shorter.begin(), shorter.end());
    }
  if (memory == 1)
    st.push_back("13");
  for (auto w : st) {
    Bounds r{.25, .8};
    for (char d : w)
      r = {1 / (d - '0' + r.hi), 1 / (d - '0' + r.lo)};
    shape_lookup[w] = shapes.size();
    longest_shape = max(longest_shape, int(w.size()));
    shapes.push_back({w, state(w), r});
  }
  for (int i = 0; i < bins; i++)
    qb.push_back({pow(base, i + 1), pow(base, i)});
}
Cell make_cell(int si, int ti, int p, int qi, bool order_points = true) {
  Cell c;
  c.s = si;
  c.t = ti;
  c.p = p;
  c.qi = qi;
  c.r = shapes[si].r;
  c.sb = shapes[ti].r;
  c.q = qb[qi];
  auto &points = shared_pools[{shapes[si].state, shapes[ti].state}];
  if (!points)
    points = make_shared<vector<Pt>>(pool(shapes[si].state, shapes[ti].state));
  c.pool.points = points;
  if (order_points) {
    c.order.resize(c.pool.size());
    iota(c.order.begin(), c.order.end(), 0);
    vector<double> values(c.pool.size());
    for (int i = 0; i < (int)c.pool.size(); ++i)
      values[i] = val(c, c.pool[i]);
    sort(c.order.begin(), c.order.end(),
         [&](int i, int j) { return values[i] < values[j]; });
    c.dom.push_back({c.order.front(), c.order.back()});
  }
  return c;
}
template <class Resolver> void prepare_moves(Cell &c, Resolver resolve) {
  for (int total = 1; total <= maxstep; total++)
    for (int i = 0; i <= total; i++)
      for (auto u : words(shapes[c.s].state, i))
        for (auto v : words(shapes[c.t].state, total - i)) {
          auto l = mat(u), r = mat(v);
          auto f = [](array<double, 4> m, double r) {
            return ((m[2] * anchor + m[3]) + r * (m[0] * anchor + m[1])) /
                   (1 + r * anchor);
          };
          double ll = f(l, c.r.lo), lh = f(l, c.r.hi), rl = f(r, c.sb.lo),
                 rh = f(r, c.sb.hi);
          double lo = c.q.lo * pow(min(ll, lh) / max(rl, rh), 2),
                 hi = c.q.hi * pow(max(ll, lh) / min(rl, rh), 2);
          if (lo < qb[bins - 1].lo - 1e-14 || hi > 1 / qb[bins - 1].lo + 1e-14)
            continue;
          int ss = dst(c.s, u), tt = dst(c.t, v),
              p = c.p * (total % 2 ? -1 : 1);
          Move move;
          move.u = u;
          move.v = v;
          move.sl = shapes[ss].state;
          move.sr = shapes[tt].state;
          for (int sw = 0; sw < 2; sw++) {
            double low = sw ? 1 / hi : lo, high = sw ? 1 / lo : hi;
            high = min(1.0, high);
            if (low > high + 1e-14)
              continue;
            int first = max(0, int(floor(log(high) / log(base))) - 1);
            int last = min(bins - 1, int(floor(log(low) / log(base))) + 1);
            for (int j = first; j <= last; j++)
              if (max(qb[j].lo, low) < min(qb[j].hi, high) - 1e-14)
                move.deps.push_back(
                    {resolve(sw ? tt : ss, sw ? ss : tt, p, j), bool(sw),
                     {max(qb[j].lo, low), min(qb[j].hi, high)}});
          }
          auto key = make_tuple(move.sl, move.sr, u, v);
          auto it = mapped_cache.find(key);
          if (it == mapped_cache.end()) {
            auto ps = make_shared<vector<Pt>>();
            for (Pt z : pool(move.sl, move.sr))
              ps->push_back({phi(u, z.x), phi(v, z.y)});
            it = mapped_cache.emplace(key, ps).first;
          }
          move.mapped = it->second;
          c.moves.push_back(move);
        }
}
void prepare() {
  prepare_catalog();
  for (int si = 0; si < (int)shapes.size(); si++)
    for (int ti = 0; ti < (int)shapes.size(); ti++)
      for (int p : {1, -1})
        for (int qi = 0; qi < bins; qi++)
          cells.push_back(make_cell(si, ti, p, qi));
  long offers = 0;
  for (auto &c : cells) {
    prepare_moves(c, id);
    offers += c.moves.size();
  }
  cerr << "prepared " << cells.size() << " cells, " << offers << " moves, "
       << cells[0].pool.size() << " endpoint pairs\n";
}
struct Membership {
  vector<Bits> normal, swapped;
};
bool subset(const Bits &a, const Bits &b) {
  for (int i = 0; i < (int)a.size(); i++)
    if (a[i] & ~b[i])
      return false;
  return true;
}
void maximal(vector<Bits> &out, Bits v) {
  int count = 0;
  for (auto x : v)
    count += __builtin_popcountll(x);
  if (count < 2)
    return;
  for (auto &b : out)
    if (subset(v, b))
      return;
  out.erase(remove_if(out.begin(), out.end(),
                      [&](const Bits &b) { return subset(b, v); }),
            out.end());
  out.push_back(move(v));
}
const Bits &bound_mask(Cell &c, Pt z, bool above) {
  auto key = make_tuple(z.x, z.y, above);
  auto it = c.bound_cache.find(key);
  if (it != c.bound_cache.end())
    return it->second;
  Bits v((c.pool.size() + 63) / 64);
  for (int i = 0; i < (int)c.pool.size(); i++)
    if (above ? ge(c, c.pool[i], z) : ge(c, z, c.pool[i]))
      v[i / 64] |= 1ULL << (i % 64);
  return c.bound_cache.emplace(key, move(v)).first->second;
}
Bits range_mask(Cell &c, Pt lo, Pt hi) {
  const auto &a = bound_mask(c, lo, true);
  const auto &b = bound_mask(c, hi, false);
  Bits v(a.size());
  for (int j = 0; j < (int)v.size(); j++)
    v[j] = a[j] & b[j];
  return v;
}
vector<Membership> memberships() {
  vector<Membership> all;
  for (auto &c : cells) {
    Membership mm;
    int n = c.pool.size(), nx = sides[shapes[c.s].state].size(),
        ny = sides[shapes[c.t].state].size();
    for (auto ab : c.dom) {
      Bits v = range_mask(c, c.pool[ab.first], c.pool[ab.second]), w(v.size());
      for (int i = 0; i < n; i++)
        if (v[i / 64] & (1ULL << (i % 64))) {
          int j = (i % ny) * nx + i / ny;
          w[j / 64] |= 1ULL << (j % 64);
        }
      maximal(mm.normal, v);
      maximal(mm.swapped, w);
    }
    all.push_back(move(mm));
  }
  return all;
}
struct Offer {
  Pt lo, hi;
  int move, a, b;
  Bits allowed;
};
template <class GetMembership>
vector<Offer> offers_from(const Cell &c, GetMembership get_membership,
                          bool require_extrema_order = true,
                          int only_move = -1) {
  vector<Offer> out;
  for (int mi = 0; mi < (int)c.moves.size(); mi++) {
    if (only_move >= 0 && mi != only_move)
      continue;
    auto &m = c.moves[mi];
    int n = m.mapped->size();
    Bits full((n + 63) / 64, ~0ULL);
    if (n % 64)
      full.back() = (1ULL << (n % 64)) - 1;
    vector<Bits> groups = {full};
    for (auto dep : m.deps) {
      const auto &membership = get_membership(dep.cell);
      const auto &members = dep.swap ? membership.swapped : membership.normal;
      vector<Bits> next;
      for (auto &g : groups)
        for (auto &member : members) {
          Bits v(g.size());
          for (int j = 0; j < (int)g.size(); j++)
            v[j] = g[j] & member[j];
          maximal(next, move(v));
        }
      groups = move(next);
      if (groups.empty())
        break;
    }
    for (auto &g : groups) {
      int low = -1, high = -1;
      double lowval = 1e99, highval = -1e99;
      for (int j = 0; j < (int)g.size(); j++) {
        uint64_t x = g[j];
        while (x) {
          int k = __builtin_ctzll(x), i = 64 * j + k;
          x &= x - 1;
          double t = val(c, (*m.mapped)[i]);
          if (t < lowval) {
            lowval = t;
            low = i;
          }
          if (t > highval) {
            highval = t;
            high = i;
          }
        }
      }
      if (low >= 0 && low != high &&
          (!require_extrema_order ||
           ge(c, (*m.mapped)[high], (*m.mapped)[low])))
        out.push_back({(*m.mapped)[low], (*m.mapped)[high], mi, low, high, g});
    }
  }
  return out;
}
vector<Offer> offers(const Cell &c, const vector<Membership> &all) {
  return offers_from(c,
                     [&](int cid) -> const Membership & { return all[cid]; });
}
vector<pair<int, int>> update(Cell &c, vector<Offer> os) {
  sort(os.begin(), os.end(),
       [&](auto a, auto b) { return val(c, a.lo) < val(c, b.lo); });
  vector<pair<Pt, Pt>> merged;
  for (auto o : os) {
    if (!merged.empty() && ge(c, merged.back().second, o.lo)) {
      if (ge(c, o.hi, merged.back().second))
        merged.back().second = o.hi;
    } else
      merged.push_back({o.lo, o.hi});
  }
  vector<pair<int, int>> result;
  vector<Bits> old_masks;
  for (auto old : c.dom)
    old_masks.push_back(range_mask(c, c.pool[old.first], c.pool[old.second]));
  for (auto ab : merged) {
    Bits mask = range_mask(c, ab.first, ab.second);
    for (auto &old : old_masks) {
      Bits v(mask.size());
      for (int j = 0; j < (int)v.size(); j++)
        v[j] = mask[j] & old[j];
      int lo = -1, hi = -1;
      for (int i : c.order)
        if (v[i / 64] & (1ULL << (i % 64))) {
          if (lo < 0)
            lo = i;
          hi = i;
        }
      if (lo >= 0 && hi != lo && ge(c, c.pool[hi], c.pool[lo]))
        result.push_back({lo, hi});
    }
  }
  sort(result.begin(), result.end(), [&](auto a, auto b) {
    return val(c, c.pool[a.first]) < val(c, c.pool[b.first]);
  });
  vector<pair<int, int>> merged_result;
  for (auto ab : result) {
    if (!merged_result.empty() &&
        ge(c, c.pool[merged_result.back().second], c.pool[ab.first])) {
      if (ge(c, c.pool[ab.second], c.pool[merged_result.back().second]))
        merged_result.back().second = ab.second;
    } else
      merged_result.push_back(ab);
  }
  return merged_result;
}

struct Edge {
  Offer offer;
  vector<pair<int, bool>> targets;
};
struct Node {
  int cid, lo, hi;
  bool covered = false;
  vector<Edge> edges;
};
struct Graph {
  vector<Node> nodes;
  bool closed = false;
  int open = 0;
  long processed_tasks = 0, queued_tasks = 0;
};
Graph trace(int root, const vector<Membership> &mem, int budget = work_budget) {
  Graph graph;
  if (root < 0 || cells[root].dom.empty())
    return graph;
  map<int, vector<Offer>> cached;
  cached[root] = offers(cells[root], mem);
  auto initial_domains = update(cells[root], cached[root]);
  if (initial_domains.empty())
    return graph;
  pair<int, int> initial = initial_domains[0];
  double best = -1;
  for (auto ab : initial_domains) {
    double w = val(cells[root], cells[root].pool[ab.second]) -
               val(cells[root], cells[root].pool[ab.first]);
    if (w > best) {
      initial = ab;
      best = w;
    }
  }
  map<int, vector<int>> family;
  vector<int> queue;
  vector<bool> queued;
  auto add = [&](int cid, int lo, int hi) {
    auto &c = cells[cid];
    for (int i : family[cid]) {
      auto &n = graph.nodes[i];
      if (ge(c, c.pool[lo], c.pool[n.lo]) && ge(c, c.pool[n.hi], c.pool[hi]))
        return i;
    }
    for (int i : family[cid]) {
      auto &n = graph.nodes[i];
      if (!ge(c, c.pool[n.hi], c.pool[lo]) || !ge(c, c.pool[hi], c.pool[n.lo]))
        continue;
      int low = -1, high = -1;
      if (ge(c, c.pool[n.lo], c.pool[lo]))
        low = lo;
      else if (ge(c, c.pool[lo], c.pool[n.lo]))
        low = n.lo;
      if (ge(c, c.pool[n.hi], c.pool[hi]))
        high = n.hi;
      else if (ge(c, c.pool[hi], c.pool[n.hi]))
        high = hi;
      if (low < 0 || high < 0)
        continue;
      n.lo = low;
      n.hi = high;
      n.covered = false;
      n.edges.clear();
      if (!queued[i]) {
        queue.push_back(i);
        queued[i] = true;
      }
      return i;
    }
    int n = graph.nodes.size();
    graph.nodes.push_back({cid, lo, hi, false, {}});
    family[cid].push_back(n);
    queue.push_back(n);
    queued.push_back(true);
    return n;
  };
  add(root, initial.first, initial.second);
  for (int work = 0; work < (int)queue.size() && work < budget; work++) {
    graph.processed_tasks = work + 1;
    int ni = queue[work];
    queued[ni] = false;
    int old_lo = graph.nodes[ni].lo, old_hi = graph.nodes[ni].hi;
    int cid = graph.nodes[ni].cid;
    auto &c = cells[cid];
    Pt current = c.pool[graph.nodes[ni].lo], end = c.pool[graph.nodes[ni].hi];
    auto it = cached.find(cid);
    if (it == cached.end())
      it = cached.emplace(cid, offers(c, mem)).first;
    auto &os = it->second;
    vector<Edge> edges;
    bool failed = false;
    for (int step = 0; !ge(c, current, end); step++) {
      int best = -1;
      double progress = val(c, current) + 1e-12, best_width = 1e99;
      Offer chosen;
      for (int j = 0; j < (int)os.size(); j++)
        if (ge(c, current, os[j].lo) && ge(c, os[j].hi, current)) {
          auto o = os[j];
          auto &m = c.moves[o.move];
          int nx = sides[m.sl].size(), ny = sides[m.sr].size();
          int lower = o.a, upper = o.b;
          double lower_value = val(c, o.lo), upper_value = val(c, o.hi);
          bool reaches = ge(c, o.hi, end);
          for (int z = 0; z < (int)m.mapped->size(); z++)
            if (o.allowed[z / 64] & (1ULL << (z % 64))) {
              Pt point = (*m.mapped)[z];
              double vv = val(c, point);
              if (vv > lower_value && ge(c, current, point)) {
                lower = z;
                lower_value = vv;
              }
              if (reaches && vv < upper_value && ge(c, point, end)) {
                upper = z;
                upper_value = vv;
              }
            }
          o.a = lower;
          o.b = upper;
          o.lo = (*m.mapped)[lower];
          o.hi = (*m.mapped)[upper];
          bool ok =
              ge(c, o.hi, current) && upper_value > val(c, current) + 1e-12;
          for (auto dep : m.deps) {
            int ia = dep.swap ? (o.a % ny) * nx + o.a / ny : o.a,
                ib = dep.swap ? (o.b % ny) * nx + o.b / ny : o.b;
            auto &d = cells[dep.cell];
            if (!ge(d, d.pool[ia], d.pool[ib]) &&
                !ge(d, d.pool[ib], d.pool[ia])) {
              ok = false;
              break;
            }
          }
          double reach = min(upper_value, val(c, end)),
                 width = upper_value - lower_value;
          if (ok && (reach > progress + 1e-12 ||
                     (abs(reach - progress) < 1e-12 && width < best_width))) {
            best = j;
            progress = reach;
            best_width = width;
            chosen = o;
          }
        }
      if (best < 0 || step > (int)os.size()) {
        failed = true;
        break;
      }
      auto o = chosen;
      auto &m = c.moves[o.move];
      Edge edge;
      edge.offer = o;
      int nx = sides[m.sl].size(), ny = sides[m.sr].size();
      for (auto dep : m.deps) {
        int ia = dep.swap ? (o.a % ny) * nx + o.a / ny : o.a,
            ib = dep.swap ? (o.b % ny) * nx + o.b / ny : o.b;
        auto &d = cells[dep.cell];
        if (!ge(d, d.pool[ib], d.pool[ia]))
          swap(ia, ib);
        edge.targets.push_back({add(dep.cell, ia, ib), dep.swap});
      }
      edges.push_back(edge);
      current = o.hi;
    }
    if (graph.nodes[ni].lo == old_lo && graph.nodes[ni].hi == old_hi) {
      graph.nodes[ni].covered = !failed && ge(c, current, end);
      graph.nodes[ni].edges = move(edges);
    }
  }
  graph.queued_tasks = queue.size();
  vector<int> remap(graph.nodes.size(), -1), visit = {0};
  remap[0] = 0;
  for (int k = 0; k < (int)visit.size(); k++)
    for (auto &e : graph.nodes[visit[k]].edges)
      for (auto target : e.targets)
        if (remap[target.first] < 0) {
          remap[target.first] = visit.size();
          visit.push_back(target.first);
        }
  vector<Node> retained;
  for (int i : visit) {
    Node n = graph.nodes[i];
    for (auto &e : n.edges)
      for (auto &t : e.targets)
        t.first = remap[t.first];
    retained.push_back(move(n));
  }
  graph.nodes = move(retained);
  for (auto &n : graph.nodes)
    graph.open += !n.covered;
  graph.closed = graph.open == 0 && !graph.nodes.empty();
  return graph;
}
void write_label(ostream &o, int sl, int sr, int i) {
  int ny = sides[sr].size();
  auto a = labels[sl][i / ny], b = labels[sr][i % ny];
  o << "[\"" << a.first << "\"," << (a.second ? "true" : "false") << ",\""
    << b.first << "\"," << (b.second ? "true" : "false") << "]";
}
void save(string path, const Graph &g, const vector<array<long, 7>> &history) {
  ofstream o(path);
  o << setprecision(17);
  o << "{\"root_prefixes\":[\"" << root_left << "\",\"" << root_right
    << "\"],\"status\":\"floating discovery; exact replay "
       "required\",\"settings\":{\"menu_depth\":"
    << menu << ",\"pool\":\"" << pool_mode << "\",\"grid_power\":" << grid_power
    << ",\"memory\":" << memory << ",\"bins\":" << bins << ",\"base\":" << base
    << ",\"max_step\":" << maxstep
    << "},\"closed_candidate\":" << (g.closed ? "true" : "false")
    << ",\"open_nodes\":" << g.open
    << ",\"processed_tasks\":" << g.processed_tasks
    << ",\"queued_tasks\":" << g.queued_tasks << ",\"history\":[";
  for (int i = 0; i < (int)history.size(); i++) {
    if (i)
      o << ",";
    auto r = history[i];
    o << "{\"round\":" << r[0] << ",\"active_cells\":" << r[1]
      << ",\"components\":" << r[2] << ",\"changed_cells\":" << r[3]
      << ",\"root_components\":" << r[4] << ",\"graph_nodes\":" << r[5]
      << ",\"open_nodes\":" << r[6] << "}";
  }
  o << "],\"roots\":[";
  if (!g.nodes.empty())
    o << 0;
  o << "],\"nodes\":[";
  for (int i = 0; i < (int)g.nodes.size(); i++) {
    if (i)
      o << ",";
    auto &n = g.nodes[i];
    auto &c = cells[n.cid];
    auto ab = make_pair(n.lo, n.hi);
    o << "{\"id\":" << i << ",\"states\":[\"" << shapes[c.s].word << "\",\""
      << shapes[c.t].word << "\"],\"parity\":" << c.p
      << ",\"ratio_bin\":" << c.qi << ",\"lower\":";
    write_label(o, shapes[c.s].state, shapes[c.t].state, ab.first);
    o << ",\"upper\":";
    write_label(o, shapes[c.s].state, shapes[c.t].state, ab.second);
    o << ",\"covered\":" << (n.covered ? "true" : "false") << ",\"children\":[";
    for (int j = 0; j < (int)n.edges.size(); j++) {
      if (j)
        o << ",";
      auto &e = n.edges[j];
      auto &m = c.moves[e.offer.move];
      o << "{\"suffixes\":[\"" << m.u << "\",\"" << m.v << "\"],\"lower\":";
      write_label(o, m.sl, m.sr, e.offer.a);
      o << ",\"upper\":";
      write_label(o, m.sl, m.sr, e.offer.b);
      o << ",\"destinations\":[";
      for (int k = 0; k < (int)e.targets.size(); k++) {
        if (k)
          o << ",";
        o << "{\"node\":" << e.targets[k].first
          << ",\"swap\":" << (e.targets[k].second ? "true" : "false") << "}";
      }
      o << "]}";
    }
    o << "]}";
  }
  o << "]}\n";
}
#ifndef KF131_SEARCH_LIBRARY
int main(int argc, char **argv) {
  if (argc > 1)
    menu = stoi(argv[1]);
  if (argc > 2)
    memory = stoi(argv[2]);
  if (argc > 3)
    bins = stoi(argv[3]);
  if (argc > 4)
    base = stod(argv[4]);
  if (argc > 5)
    maxstep = stoi(argv[5]);
  int rounds = argc > 6 ? stoi(argv[6]) : 60;
  string output = argc > 7 ? argv[7] : "";
  if (argc > 8)
    work_budget = stoi(argv[8]);
  if (argc > 9)
    pool_mode = argv[9];
  if (argc > 10)
    grid_power = stoi(argv[10]);
  if (menu < 1 || memory < 1 || bins < 1 || base <= 0 || base >= 1 ||
      maxstep < 1 || rounds < 1 || work_budget < 1 || grid_power < 1 ||
      grid_power > 10 ||
      (pool_mode != "grid" && pool_mode != "mixed" && pool_mode != "extrema")) {
    cerr << "invalid search settings\n";
    return 2;
  }
  root_left = "112" + string(memory, '2');
  root_right = "122" + string(memory, '2');
  prepare();
  int root = -1;
  for (int i = 0; i < (int)cells.size(); i++) {
    auto &c = cells[i];
    if (root_left.size() >= shapes[c.s].word.size() &&
        root_right.size() >= shapes[c.t].word.size() &&
        root_left.substr(root_left.size() - shapes[c.s].word.size()) ==
            shapes[c.s].word &&
        root_right.substr(root_right.size() - shapes[c.t].word.size()) ==
            shapes[c.t].word &&
        c.p == 1 && c.q.lo <= .5 && .5 <= c.q.hi)
      root = i;
  }
  vector<array<long, 7>> history;
  for (int n = 0; n < rounds; n++) {
    auto all = memberships();
    Graph g;
    if (n >= 3 && !output.empty()) {
      g = trace(root, all);
      cerr << "trace " << n << " nodes " << g.nodes.size() << " open " << g.open
           << " closed " << g.closed << endl;
      if (g.closed) {
        history.push_back({n, 0, 0, 0,
                           root < 0 ? -1 : long(cells[root].dom.size()),
                           long(g.nodes.size()), g.open});
        save(output, g, history);
        return 0;
      }
    }
    vector<vector<pair<int, int>>> next;
    long changed = 0, active = 0, components = 0;
    for (auto &c : cells) {
      auto d = c.dom.empty() ? c.dom : update(c, offers(c, all));
      changed += d != c.dom;
      active += !d.empty();
      components += d.size();
      next.push_back(d);
    }
    for (int i = 0; i < (int)cells.size(); i++)
      cells[i].dom = next[i];
    history.push_back({n, active, components, changed,
                       root < 0 ? -1 : long(cells[root].dom.size()),
                       long(g.nodes.size()), g.open});
    cout << "round " << n << " active " << active << " components "
         << components << " changed " << changed << " root "
         << (root < 0 ? -1 : int(cells[root].dom.size())) << endl;
    if (!changed)
      break;
    // Save the CURRENT graph before changing its endpoint table on another
    // round.
    if (!output.empty()) {
      auto mm = memberships();
      auto gg = trace(root, mm);
      save(output, gg, history);
    }
  }
}
#endif
