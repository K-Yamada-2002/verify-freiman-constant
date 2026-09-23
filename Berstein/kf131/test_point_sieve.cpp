#define KF131_BLOCK_LIBRARY
#include "block_type_search.cpp"
#include "point_sieve.hpp"
#include "realize_type_seed.hpp"
#include <cassert>
#include <random>
int main() {
  std::mt19937 rng(131);
  for (int trial = 0; trial < 300; ++trial) {
    vector<Bounds> a, b;
    double x = 0, y = 0;
    for (int i = 0; i < 30; ++i) {
      x += double(rng() % 20) / 100;
      y += double(rng() % 20) / 100;
      a.push_back({x, x + .01});
      b.push_back({y, y + .01});
      x += .02;
      y += .02;
    }
    for (int k = 0; k < 30; ++k) {
      double point = double(rng() % 10000) / 1000;
      bool brute = false;
      for (auto l : a)
        for (auto r : b)
          brute = brute || (l.lo + r.lo <= point + 1e-11 &&
                            point - 1e-11 <= l.hi + r.hi);
      assert(point_in_interval_sum(a, b, point) == brute);
    }
  }
  menu = 1;
  memory = 3;
  bins = 72;
  base = .96;
  prepare_catalog();
  cout << '[';
  bool first = true;
  for (auto l : {"222", "111", "213", "132"})
    for (auto r : {"222", "111"})
      for (int p : {1, -1})
        for (int q : {1, 15, 35, 65}) {
          int cid = lazy_cell(shape_lookup.at(l), shape_lookup.at(r), p, q);
          auto seed = realize_cell(cid);
          if (!seed)
            continue;
          if (!first)
            cout << ',';
          first = false;
          cout << "{\"states\":[\"" << l << "\",\"" << r
               << "\"],\"parity\":" << p << ",\"ratio_bin\":" << q
               << ",\"root_prefixes\":[\"" << seed->first << "\",\""
               << seed->second << "\"]}";
        }
  cout << "]\n";
}
