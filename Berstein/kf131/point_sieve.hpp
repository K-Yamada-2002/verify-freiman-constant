// Discovery-only deep rejection filter. Point membership in the sum of
// two ordered interval families takes linear time, without forming every
// pairwise interval sum. Positive answers are NOT used as a proof.
#pragma once
bool point_in_interval_sum(const vector<Bounds> &left,
                           const vector<Bounds> &right, double point) {
  size_t i = 0;
  int j = int(right.size()) - 1;
  while (i < left.size() && j >= 0) {
    if (left[i].hi + right[j].hi < point - 1e-11)
      ++i;
    else if (left[i].lo + right[j].lo > point + 1e-11)
      --j;
    else
      return true;
  }
  return false;
}
int sieve_depth = 0, sieve_points = 5;
long sieve_queries = 0, sieve_rejections = 0;
map<Block, bool> sieve_cache;
map<int, pair<vector<Bounds>, vector<Bounds>>> sieve_families;
deque<int> sieve_fifo;
bool feedback_sieve(Block key) {
  if (!sieve_depth)
    return true;
  auto old = sieve_cache.find(key);
  if (old != sieve_cache.end())
    return old->second;
  check_time();
  ++sieve_queries;
  auto [cid, lo, hi] = key;
  if (!sieve_families.count(cid)) {
    if (sieve_fifo.size() == 16) {
      sieve_families.erase(sieve_fifo.front());
      sieve_fifo.pop_front();
    }
    const auto &c = cells[cid];
    auto [r, s, h] = outer_sample(c, 0);
    const auto &tails = outer_level(sieve_depth);
    auto f = [](double x, double shape) {
      return pow(1 + shape * anchor, 2) * x / (1 + shape * x);
    };
    pair<vector<Bounds>, vector<Bounds>> families;
    for (auto interval : tails[shapes[c.s].state])
      families.first.push_back({f(interval.lo, r), f(interval.hi, r)});
    for (auto interval : tails[shapes[c.t].state]) {
      double a = c.p * h * f(interval.lo, s), b = c.p * h * f(interval.hi, s);
      families.second.push_back({min(a, b), max(a, b)});
    }
    for (auto *family : {&families.first, &families.second})
      sort(family->begin(), family->end(),
           [](auto a, auto b) { return a.lo < b.lo; });
    sieve_families.emplace(cid, move(families));
    sieve_fifo.push_back(cid);
  }
  double center = sample_value(cells[cid], {anchor, anchor}, 0);
  const auto &families = sieve_families.at(cid);
  bool possible = true;
  for (int i = 0; i < sieve_points; ++i) {
    double t =
        (double(lo) + double(hi - lo) * i / (sieve_points - 1)) / atlas_grid;
    if (!point_in_interval_sum(families.first, families.second, center + t)) {
      possible = false;
      break;
    }
  }
  sieve_rejections += !possible;
  sieve_cache[key] = possible;
  return possible;
}
