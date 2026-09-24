#include "weighted_interval_cover.hpp"
#include <cassert>
#include <iostream>
#include <random>
int main() {
  std::mt19937 rng(131);
  for (int trial = 0; trial < 3000; ++trial) {
    std::vector<WeightedInterval> a;
    int n = 1 + rng() % 10;
    for (int i = 0; i < n; ++i) {
      int lo = int(rng() % 10) - 2, hi = lo + 1 + rng() % 7;
      a.push_back({double(lo), double(hi), double(1 + rng() % 15)});
    }
    double best = std::numeric_limits<double>::infinity();
    for (int mask = 1; mask < (1 << n); ++mask) {
      std::vector<std::pair<double, double>> parts;
      double cost = 0;
      for (int i = 0; i < n; ++i)
        if (mask & (1 << i)) {
          parts.push_back({a[i].lo, a[i].hi});
          cost += a[i].cost;
        }
      std::sort(parts.begin(), parts.end());
      double right = 0;
      for (auto p : parts)
        if (p.first <= right)
          right = std::max(right, p.second);
      if (right >= 8)
        best = std::min(best, cost);
    }
    auto answer = minimum_interval_chain(a, 0, 8);
    assert(bool(answer) == std::isfinite(best));
    if (answer) {
      double current = 0, cost = 0;
      for (int i : *answer) {
        assert(a[i].lo <= current && a[i].hi > current);
        current = a[i].hi;
        cost += a[i].cost;
      }
      assert(current >= 8 && cost == best);
    }
  }
  auto a = minimum_interval_chain({{0, 8, 50}, {0, 4, 1}, {4, 8, 1}}, 0, 8);
  assert(a && *a == std::vector<int>({1, 2}));
  assert(!minimum_interval_chain({{0, 4, 1}, {4.1, 8, 1}}, 0, 8));
  assert(minimum_interval_chain({{0, 4, 1}, {4 + 1e-14, 8, 1}}, 0, 8, 1e-13,
                                1e-14));
  std::cout << "3000 exhaustive subset comparisons, gaps and contacts passed\n";
}
