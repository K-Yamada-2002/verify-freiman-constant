// A fixed, multiscale family of candidate endpoint intervals. For each
// ordered endpoint list, use lengths 1,2,4,... with half-length strides.
// Only the O(log n) intervals crossing a contact are generated there.
// Failure-interval dominance is a discovery heuristic, not an exact
// impossibility claim. The independent checker validates every success.
struct IndexedOffer {
  int move;
  vector<int> order;
  vector<double> values;
};
map<int, vector<IndexedOffer>> dyadic_banks;
map<int, vector<pair<int, int>>> failed_intervals;
long dominated_rejections = 0, learned_intervals = 0;

bool dominated_type(const TypeKey &key) {
  auto [cid, lo, hi] = key;
  auto found = failed_intervals.find(cid);
  if (found == failed_intervals.end())
    return false;
  const auto &c = cells[cid];
  double low = val(c, c.pool[lo]), high = val(c, c.pool[hi]);
  for (auto ab : found->second) {
    if (val(c, c.pool[ab.first]) + 1e-12 < low ||
        high + 1e-12 < val(c, c.pool[ab.second]))
      continue;
    if (ge(c, c.pool[ab.first], c.pool[lo]) &&
        ge(c, c.pool[hi], c.pool[ab.second])) {
      ++dominated_rejections;
      return true;
    }
  }
  return false;
}
void learn_failed_interval(const TypeKey &key) {
  if (dominated_type(key))
    return;
  int cid = get<0>(key), lo = get<1>(key), hi = get<2>(key);
  auto &intervals = failed_intervals[cid];
  const auto &c = cells[cid];
  intervals.erase(remove_if(intervals.begin(), intervals.end(),
                            [&](auto ab) {
                              return ge(c, c.pool[lo], c.pool[ab.first]) &&
                                     ge(c, c.pool[ab.second], c.pool[hi]);
                            }),
                  intervals.end());
  intervals.push_back({lo, hi});
  ++learned_intervals;
}
const vector<IndexedOffer> &dyadic_bank(int cid) {
  auto found = dyadic_banks.find(cid);
  if (found != dyadic_banks.end())
    return found->second;
  const auto &c = cells[cid];
  vector<IndexedOffer> out;
  for (const auto &offer : lazy_bank(cid, lookahead)) {
    IndexedOffer item;
    item.move = offer.move;
    const auto &points = *c.moves[item.move].mapped;
    vector<pair<double, int>> sorted;
    for (int block = 0; block < int(offer.allowed.size()); ++block) {
      uint64_t remaining = offer.allowed[block];
      while (remaining) {
        int i = 64 * block + __builtin_ctzll(remaining);
        remaining &= remaining - 1;
        sorted.push_back({val(c, points[i]), i});
      }
    }
    sort(sorted.begin(), sorted.end());
    for (auto entry : sorted) {
      item.values.push_back(entry.first);
      item.order.push_back(entry.second);
    }
    out.push_back(move(item));
  }
  return dyadic_banks.emplace(cid, move(out)).first->second;
}
vector<RepairEdge>
dyadic_alternatives(int cid, Pt current, Pt end, bool first,
                    const function<bool(const TypeKey &)> &dead) {
  const auto &c = cells[cid];
  vector<RepairEdge> out;
  double current_value = val(c, current);
  // |dA_r(x)/dr| < 3 and |A_r(x)| < 1.8 for r in [1/4,4/5], x in [0,1].
  // This bounds the variation of F(point)-F(current) around its midpoint
  // value. Initial offers with mixed-sign progress need a small extra range.
  double slack = first ? 3 * (c.r.hi - c.r.lo + c.sb.hi - c.sb.lo) +
                             1.8 * (c.q.hi - c.q.lo)
                       : 0;
  set<tuple<int, int, int>> seen;
  for (const auto &item : dyadic_bank(cid)) {
    check_time();
    int n = item.order.size();
    int before = lower_bound(item.values.begin(), item.values.end(),
                             current_value - slack - 1e-12) -
                 item.values.begin();
    int after = upper_bound(item.values.begin(), item.values.end(),
                            current_value + 1e-12) -
                item.values.begin();
    const auto &m = c.moves[item.move];
    const auto &points = *m.mapped;
    for (int span = 1; span < 2 * n; span *= 2) {
      int stride = max(1, span / 2);
      int begin = max(0, before - span - 1) / stride * stride;
      int last = min(n - 2, after - 1);
      for (int i = begin; i <= last; i += stride) {
        int j = min(n - 1, i + span), a = item.order[i], b = item.order[j];
        if (!seen.insert({item.move, a, b}).second)
          continue;
        Pt low = points[a], high = points[b];
        if (!ge(c, current, low) || !ge(c, high, low) ||
            val(c, high) <= val(c, low) + 1e-12)
          continue;
        if (first ? ge(c, current, high)
                  : (!ge(c, high, current) ||
                     val(c, high) <= current_value + 1e-12))
          continue;
        RepairEdge edge;
        edge.offer = {low, high, item.move, a, b, {}};
        bool valid = true;
        int nx = sides[m.sl].size(), ny = sides[m.sr].size();
        for (auto dep : m.deps) {
          int lo = dep.swap ? (a % ny) * nx + a / ny : a;
          int hi = dep.swap ? (b % ny) * nx + b / ny : b;
          const auto &d = cells[dep.cell];
          if (!ge(d, d.pool[hi], d.pool[lo])) {
            if (!ge(d, d.pool[lo], d.pool[hi])) {
              valid = false;
              break;
            }
            swap(lo, hi);
          }
          TypeKey key{dep.cell, lo, hi};
          if (dead(key)) {
            valid = false;
            break;
          }
          key = reuse_target(key);
          edge.cost += target_cost(key);
          edge.targets.push_back({key, dep.swap});
        }
        if (valid)
          out.push_back(move(edge));
      }
    }
  }
  sort(out.begin(), out.end(), [&](const auto &a, const auto &b) {
    if (a.cost != b.cost)
      return a.cost < b.cost;
    double av = min(val(c, a.offer.hi), val(c, end));
    double bv = min(val(c, b.offer.hi), val(c, end));
    if (av != bv)
      return av > bv;
    return val(c, a.offer.hi) - val(c, a.offer.lo) <
           val(c, b.offer.hi) - val(c, b.offer.lo);
  });
  return out;
}
optional<Game::Proposal>
dyadic_plan(const TypeKey &key, const function<bool(const TypeKey &)> &dead) {
  int cid = get<0>(key), lo = get<1>(key), hi = get<2>(key);
  const auto &c = cells[cid];
  Pt end = c.pool[hi];
  RepairPlan plan;
  auto &failed = failed_contacts[{cid, hi}];
  function<bool(Pt)> visit = [&](Pt current) {
    if (ge(c, current, end))
      return true;
    auto point = make_pair(current.x, current.y);
    if (failed.count(point))
      return false;
    check_time();
    ++expanded_contacts;
    for (auto &edge : dyadic_alternatives(cid, current, end, false, dead)) {
      plan.push_back(edge);
      if (visit(edge.offer.hi))
        return true;
      plan.pop_back();
    }
    failed.insert(point);
    return false;
  };
  for (auto &first : dyadic_alternatives(cid, c.pool[lo], end, true, dead)) {
    plan.push_back(first);
    if (visit(first.offer.hi)) {
      Game::Proposal result;
      result.plan = move(plan);
      for (const auto &edge : result.plan)
        for (const auto &target : edge.targets)
          result.children.push_back(target.first);
      return result;
    }
    plan.pop_back();
  }
  return nullopt;
}
