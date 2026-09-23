// Minimum additive-cost covering chain. Ranking only: callers still verify
// every interval and every mandatory successor using the exact checker.
#pragma once
#include <algorithm>
#include <cmath>
#include <limits>
#include <optional>
#include <stdexcept>
#include <utility>
#include <vector>
struct WeightedInterval {
  double lo, hi, cost;
};
inline std::optional<std::vector<int>>
minimum_interval_chain(const std::vector<WeightedInterval> &offers, double lo,
                       double hi, double contact = 0, double progress = 0) {
  if (!(lo < hi))
    return std::vector<int>{};
  std::vector<double> coordinates{lo, hi};
  std::vector<int> order;
  for (int i = 0; i < int(offers.size()); ++i) {
    const auto &e = offers[i];
    if (!std::isfinite(e.cost) || e.cost <= 0)
      throw std::invalid_argument("cover costs must be finite and positive");
    if (e.hi > lo + progress && e.lo <= hi + contact) {
      coordinates.push_back(std::min(hi, e.hi));
      order.push_back(i);
    }
  }
  std::sort(coordinates.begin(), coordinates.end());
  coordinates.erase(std::unique(coordinates.begin(), coordinates.end()),
                    coordinates.end());
  std::sort(order.begin(), order.end(), [&](int a, int b) {
    return std::make_pair(std::min(hi, offers[a].hi), a) <
           std::make_pair(std::min(hi, offers[b].hi), b);
  });
  using Value = std::pair<double, int>;
  const Value infinity{std::numeric_limits<double>::infinity(), -1};
  int n = 1;
  while (n < int(coordinates.size()))
    n *= 2;
  std::vector<Value> tree(2 * n, infinity);
  std::vector<int> previous(coordinates.size(), -1),
      edge(coordinates.size(), -1);
  auto update = [&](int p, Value value) {
    for (tree[p += n] = value; p > 1; p /= 2)
      tree[p / 2] = std::min(tree[p], tree[p ^ 1]);
  };
  auto query = [&](int a, int b) {
    Value best = infinity;
    for (a += n, b += n; a < b; a /= 2, b /= 2) {
      if (a & 1)
        best = std::min(best, tree[a++]);
      if (b & 1)
        best = std::min(best, tree[--b]);
    }
    return best;
  };
  update(0, {0, 0});
  for (int i : order) {
    const auto &e = offers[i];
    double end = std::min(hi, e.hi);
    int dest = std::lower_bound(coordinates.begin(), coordinates.end(), end) -
               coordinates.begin();
    int start = std::lower_bound(coordinates.begin(), coordinates.end(),
                                 e.lo - contact) -
                coordinates.begin();
    // A transition must increase coverage. Never use same-endpoint states.
    int stop = std::lower_bound(coordinates.begin(), coordinates.end(),
                                end - progress) -
               coordinates.begin();
    if (start >= stop)
      continue;
    auto best = query(start, stop);
    double cost = best.first + e.cost;
    if (best.second >= 0 && cost < tree[n + dest].first) {
      previous[dest] = best.second;
      edge[dest] = i;
      update(dest, {cost, dest});
    }
  }
  int current = coordinates.size() - 1;
  if (edge[current] < 0)
    return std::nullopt;
  std::vector<int> result;
  while (current) {
    result.push_back(edge[current]);
    current = previous[current];
  }
  std::reverse(result.begin(), result.end());
  return result;
}
