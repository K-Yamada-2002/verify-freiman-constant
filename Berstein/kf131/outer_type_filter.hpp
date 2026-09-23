// Discovery-only rejection filter. At fixed rational parameter samples, a
// finite cylinder union is an OUTER approximation of the tail sum. A type
// crossing one of its gaps cannot satisfy a uniform interval assertion.
// Float margins make this a conservative heuristic; final success still
// requires the independent exact graph verifier.
int outer_depth = 0, outer_samples = 3, outer_max_depth = 0;
long outer_rejections = 0, outer_queries = 0;
long outer_refinements = 0;
map<int, array<vector<Bounds>, 3>> outer_levels;
vector<int> outer_cell_depth;
map<tuple<int, int, int>, vector<Bounds>> outer_cache;
map<TypeKey, bool> outer_known;

const array<vector<Bounds>, 3> &outer_level(int depth) {
  auto existing = outer_levels.find(depth);
  if (existing != outer_levels.end()) return existing->second;
  array<vector<Bounds>, 3> levels;
  double a = (2 * sqrt(10) - 5) / 5, b = (2 * sqrt(10) - 4) / 3,
         cc = (sqrt(10) - 2) / 4, d = (2 * sqrt(10) - 5) / 3;
  array<Bounds, 3> tail = {Bounds{a, b}, Bounds{cc, b}, Bounds{a, d}};
  for (int s = 0; s < 3; ++s)
    for (auto w : words(s, depth)) {
      int t = state((s == 1 ? "1" : s == 2 ? "13" : "") + w);
      double x = phi(w, tail[t].lo), y = phi(w, tail[t].hi);
      levels[s].push_back({min(x, y), max(x, y)});
    }
  return outer_levels.emplace(depth, move(levels)).first->second;
}
void prepare_outer_filter() {
  outer_cell_depth.assign(cells.size(), outer_depth);
  if (outer_depth) outer_level(outer_depth);
}
void refine_outer_filter(int cid) {
  if (!outer_depth || outer_cell_depth[cid] >= outer_max_depth) return;
  ++outer_cell_depth[cid]; ++outer_refinements;
  auto it = outer_known.lower_bound({cid, -1, -1});
  while (it != outer_known.end() && get<0>(it->first) == cid) {
    if (it->second) it = outer_known.erase(it);
    else ++it;
  }
}
array<double, 3> outer_sample(const Cell &c, int i) {
  double r = (c.r.lo + c.r.hi) / 2, s = (c.sb.lo + c.sb.hi) / 2;
  if (i >= 3) {
    r = (i - 3) & 1 ? c.r.hi : c.r.lo;
    s = (i - 3) & 2 ? c.sb.hi : c.sb.lo;
  }
  double h = i == 0 ? (c.q.lo + c.q.hi) / 2 :
             i == 1 ? c.q.lo : i == 2 ? c.q.hi :
             ((i - 3) & 4 ? c.q.hi : c.q.lo);
  return {r, s, h};
}
double sample_value(const Cell &c, Pt point, int i) {
  auto [r, s, h] = outer_sample(c, i);
  return pow(1 + r * anchor, 2) * point.x / (1 + r * point.x) +
         c.p * h * pow(1 + s * anchor, 2) * point.y / (1 + s * point.y);
}
const vector<Bounds> &outer_intervals(int cid, int sample) {
  int depth = outer_cell_depth[cid];
  auto key = make_tuple(cid, sample, depth);
  auto found = outer_cache.find(key);
  if (found != outer_cache.end()) return found->second;
  const auto &c = cells[cid];
  const auto &tails = outer_level(depth);
  auto [r, s, h] = outer_sample(c, sample);
  auto f = [](double x, double shape) {
    return pow(1 + shape * anchor, 2) * x / (1 + shape * x);
  };
  vector<Bounds> left, right, sums, merged;
  for (auto b : tails[shapes[c.s].state])
    left.push_back({f(b.lo, r), f(b.hi, r)});
  for (auto b : tails[shapes[c.t].state]) {
    double lo = c.p * h * f(b.lo, s), hi = c.p * h * f(b.hi, s);
    right.push_back({min(lo, hi), max(lo, hi)});
  }
  sums.reserve(left.size() * right.size());
  for (auto a : left)
    for (auto b : right)
      sums.push_back({a.lo + b.lo - 1e-12, a.hi + b.hi + 1e-12});
  sort(sums.begin(), sums.end(), [](auto a, auto b) { return a.lo < b.lo; });
  for (auto b : sums) {
    if (!merged.empty() && b.lo <= merged.back().hi + 1e-11)
      merged.back().hi = max(merged.back().hi, b.hi);
    else merged.push_back(b);
  }
  return outer_cache.emplace(key, move(merged)).first->second;
}
bool outer_contains(int cid, int sample, double lo, double hi) {
  const auto &parts = outer_intervals(cid, sample);
  auto it = upper_bound(parts.begin(), parts.end(), lo + 1e-11,
                        [](double value, Bounds b) { return value < b.lo; });
  if (it == parts.begin()) return false;
  --it;
  return hi <= it->hi + 1e-11;
}
bool outer_possible(const TypeKey &key) {
  if (!outer_depth) return true;
  auto found = outer_known.find(key);
  if (found != outer_known.end()) return found->second;
  ++outer_queries;
  auto [cid, lo, hi] = key;
  const auto &c = cells[cid];
  bool possible = true;
  for (int i = 0; i < outer_samples; ++i)
    if (!outer_contains(cid, i, sample_value(c, c.pool[lo], i),
                                  sample_value(c, c.pool[hi], i))) {
      possible = false;
      ++outer_rejections;
      break;
    }
  outer_known[key] = possible;
  return possible;
}
