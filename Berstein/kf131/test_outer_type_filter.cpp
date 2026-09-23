#define KF131_REPAIR_LIBRARY
#include "repair_type_search.cpp"
#include <cassert>

int main() {
  memory = 1; menu = 1; bins = 8; base = .7; maxstep = 2;
  outer_depth = 3; outer_samples = 3;
  prepare(); prepare_outer_filter();
  int gaps = 0, rejected = 0, witnesses = 0;
  for (int cid = 0; cid < (int)cells.size(); cid += 3) {
    const auto &c = cells[cid];
    auto left = words(shapes[c.s].state, outer_depth);
    auto right = words(shapes[c.t].state, outer_depth);
    for (int sample = 0; sample < outer_samples; ++sample) {
      for (size_t k = 0; k < min(left.size(), right.size()); k += 5) {
        Pt point{phi(left[k], anchor), phi(right[right.size()-1-k], anchor)};
        double value = sample_value(c, point, sample);
        assert(outer_contains(cid, sample, value, value));
        ++witnesses;
      }
      const auto &parts = outer_intervals(cid, sample);
      assert(!parts.empty());
      assert(!outer_contains(cid, sample, parts.front().lo - .1, parts.front().lo - .1));
      for (size_t j = 1; j < parts.size(); ++j)
        if (parts[j].lo - parts[j-1].hi > 1e-8) {
          double point = (parts[j].lo + parts[j-1].hi) / 2;
          assert(!outer_contains(cid, sample, point, point));
          ++gaps;
        }
    }
    rejected += !outer_possible({cid, c.order.front(), c.order.back()});
  }
  assert(witnesses > 100 && gaps > 10 && rejected > 10);
  cout << "outer filter: " << witnesses << " periodic witnesses retained; "
       << gaps << " finite-union gaps and " << rejected << " rejected broad types\n";
}
