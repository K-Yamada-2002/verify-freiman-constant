// Uniform scalar intervals in coordinates centered at the all-2 tail.
// Decreasing finite-grid iteration; no finite frontier is accepted as filled.
// Usage: engine MEMORY BINS BASE MAX_STEP GRID ROUNDS OUTPUT
#define KF131_SEARCH_LIBRARY
#include "adaptive_type_search.cpp"
#include <cstdio>
using Segment = pair<int, int>;
using Domain = vector<Segment>;
vector<Domain> domains;
int grid = 1024;
struct ScalarCase {
  bool swap;
  Segment interval;
  vector<int> cells;
};
struct ScalarOffer {
  double lo, hi;
  int move;
  vector<ScalarCase> cases;
};

Bounds quadratic_range(string w, double k, Bounds rb) {
  auto m = mat(w);
  double d = m[2] * anchor + m[3], z = phi(w, anchor);
  auto t = [&](double r) { return (1 + r * anchor) / (1 + r * z); };
  double t0 = min(t(rb.lo), t(rb.hi)), t1 = max(t(rb.lo), t(rb.hi));
  double a = k / (d * d), b = z - anchor;
  auto f = [&](double x) { return (a * x + b) * x; };
  Bounds out{min(f(t0), f(t1)), max(f(t0), f(t1))};
  if (a != 0) {
    double critical = -b / (2 * a);
    if (t0 < critical && critical < t1) {
      out.lo = min(out.lo, f(critical));
      out.hi = max(out.hi, f(critical));
    }
  }
  return out;
}
Bounds combine(const Cell &c, Bounds l, Bounds r) {
  if (c.p < 0)
    r = {-r.hi, -r.lo};
  return {l.lo + min(c.q.lo * r.lo, c.q.hi * r.lo),
          l.hi + max(c.q.lo * r.hi, c.q.hi * r.hi)};
}
Bounds endpoint_image(const Cell &c, const Move &m, bool sw, double endpoint) {
  int eu = m.u.size() % 2 ? -1 : 1, ev = m.v.size() % 2 ? -1 : 1;
  return combine(c, quadratic_range(m.u, sw ? 0 : eu * endpoint, c.r),
                 quadratic_range(m.v, sw ? ev * endpoint : 0, c.sb));
}
Domain intersect(const Domain &a, const Domain &b) {
  Domain out;
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    int lo = max(a[i].first, b[j].first), hi = min(a[i].second, b[j].second);
    if (lo < hi)
      out.push_back({lo, hi});
    if (a[i].second < b[j].second)
      ++i;
    else
      ++j;
  }
  return out;
}
vector<ScalarOffer> scalar_offers(int cid) {
  const auto &c = cells[cid];
  vector<ScalarOffer> all;
  for (int mi = 0; mi < (int)c.moves.size(); ++mi) {
    const auto &m = c.moves[mi];
    vector<int> dependencies[2];
    for (auto d : m.deps)
      dependencies[d.swap].push_back(d.cell);
    vector<ScalarOffer> branches[2];
    for (int sw = 0; sw < 2; ++sw) {
      auto &deps = dependencies[sw];
      if (deps.empty())
        continue;
      Domain common = domains[deps.front()];
      for (size_t i = 1; i < deps.size() && !common.empty(); ++i)
        common = intersect(common, domains[deps[i]]);
      for (auto ab : common) {
        auto l = endpoint_image(c, m, sw, double(ab.first) / grid);
        auto r = endpoint_image(c, m, sw, double(ab.second) / grid);
        int sign = sw ? c.p * (m.v.size() % 2 ? -1 : 1)
                      : (m.u.size() % 2 ? -1 : 1);
        double lo = sign > 0 ? l.hi : r.hi;
        double hi = sign > 0 ? r.lo : l.lo;
        if (lo < hi)
          branches[sw].push_back({lo, hi, mi, {{bool(sw), ab, deps}}});
      }
      sort(branches[sw].begin(), branches[sw].end(),
           [](const auto &a, const auto &b) { return a.lo < b.lo; });
    }
    if (dependencies[0].empty() || dependencies[1].empty()) {
      const auto &branch = branches[dependencies[0].empty()];
      all.insert(all.end(), branch.begin(), branch.end());
    } else {
      size_t i = 0, j = 0;
      while (i < branches[0].size() && j < branches[1].size()) {
        const auto &a = branches[0][i], &b = branches[1][j];
        double lo = max(a.lo, b.lo), hi = min(a.hi, b.hi);
        if (lo < hi)
          all.push_back({lo, hi, mi, {a.cases[0], b.cases[0]}});
        if (a.hi < b.hi)
          ++i;
        else
          ++j;
      }
    }
  }
  sort(all.begin(), all.end(), [](const auto &a, const auto &b) {
    return a.lo < b.lo;
  });
  return all;
}
Domain scalar_update(int cid, const vector<ScalarOffer> &offers) {
  vector<Bounds> merged;
  for (const auto &o : offers) {
    if (!merged.empty() && o.lo <= merged.back().hi + 1e-13)
      merged.back().hi = max(merged.back().hi, o.hi);
    else
      merged.push_back({o.lo, o.hi});
  }
  Domain rounded;
  for (auto b : merged) {
    int lo = ceil(b.lo * grid - 1e-10), hi = floor(b.hi * grid + 1e-10);
    if (lo < hi)
      rounded.push_back({lo, hi});
  }
  return intersect(domains[cid], rounded);
}
void initial_domains() {
  double a = (2 * sqrt(10) - 5) / 5, b = (2 * sqrt(10) - 4) / 3,
         cc = (sqrt(10) - 2) / 4, d = (2 * sqrt(10) - 5) / 3;
  array<Bounds, 3> tails = {Bounds{a, b}, Bounds{cc, b}, Bounds{a, d}};
  for (const auto &c : cells) {
    auto l = tails[shapes[c.s].state], r = tails[shapes[c.t].state];
    auto range = [](double x, Bounds rb) {
      return Bounds{delta_min(x, anchor, rb), -delta_min(anchor, x, rb)};
    };
    auto low = combine(c, range(l.lo, c.r), range(c.p > 0 ? r.lo : r.hi, c.sb));
    auto high = combine(c, range(l.hi, c.r), range(c.p > 0 ? r.hi : r.lo, c.sb));
    int lo = ceil(low.hi * grid), hi = floor(high.lo * grid);
    domains.push_back(lo < hi ? Domain{{lo, hi}} : Domain{});
  }
}

struct ScalarNode {
  int cell, component;
  Segment interval;
  bool covered = false;
  vector<ScalarOffer> offers;
};
bool save_scalar(string output, int root, const vector<array<long, 5>> &history) {
  vector<ScalarNode> nodes;
  map<pair<int, int>, int> index;
  Segment seed_interval;
  auto add = [&](int cid, int comp) {
    auto key = make_pair(cid, comp);
    auto it = index.find(key);
    if (it != index.end())
      return it->second;
    int id = nodes.size();
    index[key] = id;
    nodes.push_back({cid, comp, comp < 0 ? seed_interval : domains[cid][comp], false, {}});
    return id;
  };
  if (root >= 0 && !domains[root].empty()) {
    auto candidates = scalar_update(root, scalar_offers(root));
    if (!candidates.empty()) {
      seed_interval = *max_element(candidates.begin(), candidates.end(), [](auto a, auto b) {
        return a.second - a.first < b.second - b.first;
      });
      int component = -1;
      for (int i = 0; i < (int)domains[root].size(); ++i)
        if (domains[root][i] == seed_interval) component = i;
      add(root, component);
    }
  }
  map<int, vector<ScalarOffer>> banks;
  for (int i = 0; i < (int)nodes.size(); ++i) {
    auto n = nodes[i];
    auto interval = n.interval;
    double current = double(interval.first) / grid, end = double(interval.second) / grid;
    if (!banks.count(n.cell))
      banks[n.cell] = scalar_offers(n.cell);
    const auto &os = banks[n.cell];
    vector<ScalarOffer> used;
    while (current < end - 1e-12) {
      const ScalarOffer *best = nullptr;
      for (const auto &o : os) {
        if (o.lo > current + 1e-12)
          break;
        if (o.hi > current + 1e-12 && (!best || o.hi > best->hi))
          best = &o;
      }
      if (!best)
        break;
      used.push_back(*best);
      current = best->hi;
    }
    if (current < end - 1e-12)
      continue;
    nodes[i].covered = true;
    nodes[i].offers = used;
    for (const auto &o : used)
      for (const auto &cs : o.cases)
        for (int cid : cs.cells) {
          bool found = false;
          for (int j = 0; j < (int)domains[cid].size(); ++j)
            if (domains[cid][j].first <= cs.interval.first &&
                cs.interval.second <= domains[cid][j].second) {
              add(cid, j);
              found = true;
              break;
            }
          if (!found)
            throw runtime_error("missing child component");
        }
  }
  int open = 0;
  for (const auto &n : nodes)
    open += !n.covered;
  bool closed = !nodes.empty() && !open;
  ofstream out(output + ".tmp");
  out << setprecision(17) << "{\"schema\":\"kf131-scalar-intervals-v1\",\"settings\":{\"base\":"
      << base << ",\"bins\":" << bins << ",\"grid\":" << grid
      << ",\"memory\":" << memory << ",\"max_step\":" << maxstep
      << "},\"root_prefixes\":[\"" << root_left << "\",\"" << root_right
      << "\"],\"roots\":[" << (nodes.empty() ? "" : "0")
      << "],\"closed_candidate\":" << (closed ? "true" : "false")
      << ",\"open_nodes\":" << open << ",\"history\":[";
  for (int i = 0; i < (int)history.size(); ++i) {
    if (i) out << ',';
    const auto &h = history[i];
    out << "{\"round\":" << h[0] << ",\"active_cells\":" << h[1]
        << ",\"components\":" << h[2] << ",\"grid_units\":" << h[3]
        << ",\"changed_cells\":" << h[4] << '}';
  }
  out << "],\"nodes\":[";
  for (int i = 0; i < (int)nodes.size(); ++i) {
    if (i) out << ',';
    const auto &n = nodes[i]; const auto &c = cells[n.cell];
    auto ab = n.interval;
    out << "{\"states\":[\"" << shapes[c.s].word << "\",\"" << shapes[c.t].word
        << "\"],\"parity\":" << c.p << ",\"ratio_bin\":" << c.qi
        << ",\"interval\":[" << ab.first << ',' << ab.second
        << "],\"covered\":" << (n.covered ? "true" : "false") << ",\"children\":[";
    for (int j = 0; j < (int)n.offers.size(); ++j) {
      if (j) out << ',';
      const auto &o = n.offers[j]; const auto &m = c.moves[o.move];
      out << "{\"suffixes\":[\"" << m.u << "\",\"" << m.v << "\"],\"cases\":[";
      for (int k = 0; k < (int)o.cases.size(); ++k) {
        if (k) out << ',';
        const auto &cs = o.cases[k];
        out << "{\"swap\":" << (cs.swap ? "true" : "false") << ",\"interval\":["
            << cs.interval.first << ',' << cs.interval.second << "],\"destinations\":[";
        for (int l = 0; l < (int)cs.cells.size(); ++l) {
          if (l) out << ',';
          int cid = cs.cells[l];
          for (int d = 0; d < (int)domains[cid].size(); ++d)
            if (domains[cid][d].first <= cs.interval.first && cs.interval.second <= domains[cid][d].second) {
              out << index.at({cid, d}); break;
            }
        }
        out << "]}";
      }
      out << "]}";
    }
    out << "]}";
  }
  out << "]}\n"; out.close();
  if (rename((output + ".tmp").c_str(), output.c_str()) != 0)
    throw runtime_error("could not save scalar graph");
  cerr << "graph " << nodes.size() << " open " << open << " closed " << closed << endl;
  return closed;
}

int main(int argc, char **argv) {
  if (argc != 8) {
    cerr << "usage: engine MEMORY BINS BASE MAX_STEP GRID ROUNDS OUTPUT\n";
    return 2;
  }
  memory = stoi(argv[1]); bins = stoi(argv[2]); base = stod(argv[3]);
  maxstep = stoi(argv[4]); grid = stoi(argv[5]); int rounds = stoi(argv[6]);
  string output = argv[7];
  if (memory < 1 || bins < 1 || base <= 0 || base >= 1 || maxstep < 1 ||
      grid < 1 || rounds < 1) return 2;
  menu = 1;
  root_left = "112" + string(memory, '2');
  root_right = "122" + string(memory, '2');
  prepare(); initial_domains();
  int root = -1;
  for (int i = 0; i < (int)cells.size(); ++i) {
    const auto &c = cells[i];
    if (shapes[c.s].word == string(memory, '2') && shapes[c.t].word == string(memory, '2') &&
        c.p == 1 && c.q.lo <= .5 && .5 <= c.q.hi) root = i;
  }
  vector<array<long, 5>> history;
  for (int round = 0; round < rounds; ++round) {
    vector<Domain> next(cells.size());
    long active = 0, components = 0, units = 0, changed = 0;
    for (int i = 0; i < (int)cells.size(); ++i) {
      if (!domains[i].empty()) next[i] = scalar_update(i, scalar_offers(i));
      changed += next[i] != domains[i]; active += !next[i].empty(); components += next[i].size();
      for (auto ab : next[i]) units += ab.second - ab.first;
    }
    domains = move(next);
    history.push_back({round, active, components, units, changed});
    cout << "round " << round << " active " << active << " components " << components
         << " units " << units << " changed " << changed << " root "
         << (root < 0 ? 0 : domains[root].size()) << endl;
    if ((round + 1) % 5 == 0 || !changed || !active || round + 1 == rounds)
      if (save_scalar(output, root, history)) return 0;
    if (!changed || !active) break;
  }
}
