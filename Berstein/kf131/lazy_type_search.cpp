// On-demand geometry and finite-cover search. Output uses the existing
// interval-type schema and is accepted only by verify_type_graph.py.
#define KF131_REPAIR_LIBRARY
#include "repair_type_search.cpp"
#include <chrono>
#include <stdexcept>

using CellKey = tuple<int, int, int, int>;
map<CellKey, int> lazy_ids;
deque<bool> moves_ready;
map<pair<int, int>, Membership> lazy_members;
map<pair<int, int>, vector<Offer>> lazy_banks;
map<pair<int, int>, vector<Offer>> selective_banks;
map<const vector<Pt> *, pair<Pt, Pt>> mapped_hulls;
map<TypeKey, bool> available_types;
long membership_queries = 0, membership_rejections = 0;
long expanded_cells = 0, created_moves = 0;
long reused_targets = 0, containment_candidates = 0;
int lookahead = 0, max_cells = 200000, seed_span = 2;
int membership_samples = 3;
string planner_mode = "adaptive";
double seconds_limit = 600;
auto search_started = chrono::steady_clock::now();
string stop_reason = "completed finite work budget";

struct SearchLimit : runtime_error {
  using runtime_error::runtime_error;
};
double elapsed() {
  return chrono::duration<double>(chrono::steady_clock::now() - search_started)
      .count();
}
void check_time() {
  if (elapsed() >= seconds_limit)
    throw SearchLimit("wall clock limit");
}
int lazy_cell(int si, int ti, int p, int qi) {
  CellKey key{si, ti, p, qi};
  auto found = lazy_ids.find(key);
  if (found != lazy_ids.end())
    return found->second;
  if (int(cells.size()) >= max_cells)
    throw SearchLimit("parameter cell limit");
  int cid = cells.size();
  cells.push_back(make_cell(si, ti, p, qi, false));
  moves_ready.push_back(false);
  outer_cell_depth.push_back(outer_depth);
  lazy_ids[key] = cid;
  return cid;
}
void lazy_moves(int cid) {
  if (moves_ready[cid])
    return;
  check_time();
  prepare_moves(cells[cid], lazy_cell);
  moves_ready[cid] = true;
  ++expanded_cells;
  created_moves += cells[cid].moves.size();
}
void transpose_membership(int cid, Membership &out) {
  auto &c = cells[cid];
  int nx = sides[shapes[c.s].state].size(),
      ny = sides[shapes[c.t].state].size();
  for (const Bits &group : out.normal) {
    Bits swapped(group.size());
    for (int block = 0; block < int(group.size()); ++block) {
      uint64_t remaining = group[block];
      while (remaining) {
        int i = 64 * block + __builtin_ctzll(remaining);
        remaining &= remaining - 1;
        int j = (i % ny) * nx + i / ny;
        swapped[j / 64] |= 1ULL << (j % 64);
      }
    }
    out.swapped.push_back(move(swapped));
  }
}
// Endpoints are classified by the outer-union component containing them
// at EACH sample. Equal signatures allow an interval between the endpoints
// at those samples. This only prunes discovery: it proves no positive rule.
Membership sampled_membership(int cid) {
  check_time();
  auto &c = cells[cid];
  int n = c.pool.size();
  vector<vector<int>> signatures(n);
  vector<bool> valid(n, true);
  for (int sample = 0; sample < membership_samples; ++sample) {
    const auto &parts = outer_intervals(cid, sample);
    for (int i = 0; i < n; ++i) {
      double value = sample_value(c, c.pool[i], sample);
      auto it = upper_bound(parts.begin(), parts.end(), value + 1e-11,
                            [](double x, Bounds b) { return x < b.lo; });
      if (it == parts.begin() || value > prev(it)->hi + 1e-11) {
        valid[i] = false;
      } else
        signatures[i].push_back(int(prev(it) - parts.begin()));
    }
  }
  map<vector<int>, Bits> groups;
  for (int i = 0; i < n; ++i)
    if (valid[i]) {
      auto &bits = groups[signatures[i]];
      if (bits.empty())
        bits.resize((n + 63) / 64);
      bits[i / 64] |= 1ULL << (i % 64);
    }
  Membership out;
  for (auto &entry : groups)
    maximal(out.normal, move(entry.second));
  transpose_membership(cid, out);
  return out;
}
const Membership &lazy_membership(int cid, int depth);
const vector<Offer> &lazy_bank(int cid, int depth) {
  auto key = make_pair(cid, depth);
  auto found = lazy_banks.find(key);
  if (found != lazy_banks.end())
    return found->second;
  lazy_moves(cid);
  auto bank = offers_from(
      cells[cid],
      [&](int child) -> const Membership & {
        return lazy_membership(child, depth);
      },
      planner_mode != "dyadic");
  return lazy_banks.emplace(key, move(bank)).first->second;
}
const Membership &lazy_membership(int cid, int depth) {
  auto key = make_pair(cid, depth);
  auto found = lazy_members.find(key);
  if (found != lazy_members.end())
    return found->second;
  if (depth == 0)
    return lazy_members.emplace(key, sampled_membership(cid)).first->second;
  check_time();
  const auto &before = lazy_membership(cid, depth - 1);
  auto offers = lazy_bank(cid, depth - 1);
  const auto &c = cells[cid];
  sort(offers.begin(), offers.end(), [&](const Offer &a, const Offer &b) {
    return val(c, a.lo) < val(c, b.lo);
  });
  vector<pair<Pt, Pt>> components;
  for (const auto &offer : offers) {
    if (!components.empty() && ge(c, components.back().second, offer.lo)) {
      if (ge(c, offer.hi, components.back().second))
        components.back().second = offer.hi;
    } else
      components.push_back({offer.lo, offer.hi});
  }
  Membership next;
  for (const auto &interval : components) {
    Bits inside = range_mask(cells[cid], interval.first, interval.second);
    for (const auto &old : before.normal) {
      Bits group(inside.size());
      for (int i = 0; i < int(group.size()); ++i)
        group[i] = inside[i] & old[i];
      maximal(next.normal, move(group));
    }
  }
  transpose_membership(cid, next);
  return lazy_members.emplace(key, move(next)).first->second;
}
bool lazy_available(const TypeKey &key) {
  auto found = available_types.find(key);
  if (found != available_types.end())
    return found->second;
  ++membership_queries;
  auto [cid, lo, hi] = key;
  const auto &member = lazy_membership(cid, lookahead);
  bool present = false;
  for (const auto &group : member.normal)
    if ((group[lo / 64] & (1ULL << (lo % 64))) &&
        (group[hi / 64] & (1ULL << (hi % 64)))) {
      present = true;
      break;
    }
  membership_rejections += !present;
  available_types[key] = present;
  return present;
}
// Avoid preparing arrivals of moves whose complete convex hull is already
// disjoint from this requested interval. All candidate rules still go to
// the independent verifier; no geometric assumption is added to a proof.
vector<Offer> target_bank(const TypeKey &key) {
  int cid = get<0>(key), lo = get<1>(key), hi = get<2>(key);
  lazy_moves(cid);
  const auto &c = cells[cid];
  vector<Offer> bank;
  for (int mi = 0; mi < int(c.moves.size()); ++mi) {
    const auto &m = c.moves[mi];
    const auto &points = *m.mapped;
    auto hull = mapped_hulls.find(&points);
    // Each mapped pool contains the extremal endpoints of the whole child.
    // The x/y extrema are independent of r,s,h.
    if (hull == mapped_hulls.end()) {
      Pt low{1., 1.}, high{0., 0.};
      for (const Pt &point : points) {
        low.x = min(low.x, point.x);
        high.x = max(high.x, point.x);
        low.y = min(low.y, point.y);
        high.y = max(high.y, point.y);
      }
      hull = mapped_hulls.emplace(&points, make_pair(low, high)).first;
    }
    Pt low = hull->second.first, high = hull->second.second;
    if (c.p < 0)
      swap(low.y, high.y);
    if (ge(c, c.pool[lo], high) || ge(c, low, c.pool[hi]))
      continue;
    auto slot = make_pair(cid, mi);
    auto found = selective_banks.find(slot);
    if (found == selective_banks.end()) {
      auto offers = offers_from(
          c,
          [&](int child) -> const Membership & {
            return lazy_membership(child, lookahead);
          },
          true, mi);
      found = selective_banks.emplace(slot, move(offers)).first;
    }
    bank.insert(bank.end(), found->second.begin(), found->second.end());
  }
  return bank;
}
vector<TypeKey> lazy_seeds(int root) {
  auto &c = cells[root];
  const auto &members = lazy_membership(root, lookahead);
  set<TypeKey> unique;
  vector<double> values(c.pool.size());
  for (int i = 0; i < int(values.size()); ++i)
    values[i] = val(c, c.pool[i]);
  for (const auto &group : members.normal) {
    vector<int> allowed;
    for (int i = 0; i < int(c.pool.size()); ++i)
      if (group[i / 64] & (1ULL << (i % 64)))
        allowed.push_back(i);
    sort(allowed.begin(), allowed.end(),
         [&](int a, int b) { return values[a] < values[b]; });
    for (int i = 0; i < int(allowed.size()); ++i) {
      int count = 0, a = allowed[i];
      for (int j = i + 1; j < int(allowed.size()) && count < seed_span; ++j) {
        int b = allowed[j];
        if (values[b] <= values[a] + 1e-10 || !ge(c, c.pool[b], c.pool[a]))
          continue;
        unique.insert({root, a, b});
        ++count;
      }
    }
  }
  vector<TypeKey> seeds(unique.begin(), unique.end());
  double center = val(c, {anchor, anchor});
  auto distance = [&](const TypeKey &key) {
    return abs((values[get<1>(key)] + values[get<2>(key)]) / 2 - center);
  };
  sort(seeds.begin(), seeds.end(), [&](const TypeKey &a, const TypeKey &b) {
    double da = distance(a), db = distance(b);
    return da != db ? da < db : a < b;
  });
  return seeds;
}
#include "dyadic_cover_search.hpp"
void lazy_snapshot(const string &output, const Game &game, int node_limit,
                   bool finished) {
  snapshot(output, game, {}, node_limit, 1., finished);
  ofstream log(output + ".lazy.json.tmp");
  log << setprecision(17) << "{\"parameter_cells\":" << cells.size()
      << ",\"expanded_cells\":" << expanded_cells
      << ",\"moves\":" << created_moves
      << ",\"membership_boxes\":" << lazy_members.size()
      << ",\"selective_move_banks\":" << selective_banks.size()
      << ",\"membership_queries\":" << membership_queries
      << ",\"membership_rejections\":" << membership_rejections
      << ",\"reused_targets\":" << reused_targets
      << ",\"containment_candidates\":" << containment_candidates
      << ",\"planner\":\"" << planner_mode << "\""
      << ",\"dominated_rejections\":" << dominated_rejections
      << ",\"learned_intervals\":" << learned_intervals
      << ",\"lookahead\":" << lookahead << ",\"max_cells\":" << max_cells
      << ",\"elapsed_seconds\":" << elapsed() << ",\"stop\":\"" << stop_reason
      << "\",\"finished\":" << (finished ? "true" : "false") << "}\n";
  log.close();
  if (rename((output + ".lazy.json.tmp").c_str(),
             (output + ".lazy.json").c_str()))
    throw runtime_error("could not save lazy progress");
}

#ifndef KF131_LAZY_LIBRARY
int main(int argc, char **argv) {
  if (argc < 16) {
    cerr << "usage: lazy MENU MEMORY BINS BASE MAX_STEP OUTPUT TYPES VARIANTS "
            "OUTER_DEPTH SAMPLES LOOKAHEAD ROOT_TRIALS ROOT_STEPS CELLS "
            "SECONDS\n";
    return 2;
  }
  menu = stoi(argv[1]);
  memory = stoi(argv[2]);
  bins = stoi(argv[3]);
  base = stod(argv[4]);
  maxstep = stoi(argv[5]);
  string output = argv[6];
  int node_limit = stoi(argv[7]);
  variants = stoi(argv[8]);
  outer_depth = outer_max_depth = stoi(argv[9]);
  outer_samples = membership_samples = stoi(argv[10]);
  lookahead = stoi(argv[11]);
  root_trials = stoi(argv[12]);
  root_step_budget = stol(argv[13]);
  max_cells = stoi(argv[14]);
  seconds_limit = stod(argv[15]);
  planner_mode = argc > 16 ? argv[16] : "adaptive";
  pool_mode = argc > 17 ? argv[17] : "extrema";
  grid_power = argc > 18 ? stoi(argv[18]) : 9;
  if (menu < 1 || menu > 5 || memory < 1 || memory > 8 || bins < 1 ||
      !(0 < base && base < 1) || maxstep < 1 || maxstep > 6 || node_limit < 1 ||
      variants < 1 || outer_depth < 1 || outer_depth > 7 ||
      (membership_samples != 1 && membership_samples != 3 &&
       membership_samples != 11) ||
      lookahead < 0 || lookahead > 3 || root_trials < 1 ||
      root_step_budget < 1 || max_cells < 1 || seconds_limit <= 0 ||
      grid_power < 3 || grid_power > 16 ||
      (pool_mode != "extrema" && pool_mode != "periodic" &&
       pool_mode != "centered") ||
      (planner_mode != "adaptive" && planner_mode != "dyadic"))
    return 2;
  strategy = "dfs-reuse";
  root_left = "112" + string(memory, '2');
  root_right = "122" + string(memory, '2');
  prepare_catalog();
  int shape = shape_lookup.at(string(memory, '2')), qi = -1;
  for (int i = 0; i < bins; ++i)
    if (qb[i].lo <= .5 && .5 <= qb[i].hi)
      qi = i;
  if (qi < 0) {
    cerr << "ratio grid must contain 1/2\n";
    return 2;
  }
  int root = lazy_cell(shape, shape, 1, qi);
  vector<TypeKey> seeds;
  try {
    seeds = lazy_seeds(root);
  } catch (const SearchLimit &error) {
    cerr << "seed preparation stopped: " << error.what() << '\n';
    save(output, Graph{}, {});
    return 0;
  }
  cerr << "lazy catalog: " << shapes.size() << " shapes, " << cells.size()
       << " created cells; " << seeds.size() << " seed intervals\n";
  if (seeds.empty()) {
    save(output, Graph{}, {});
    return 0;
  }
  Game game(seeds[0], true);
  lazy_snapshot(output, game, node_limit, false);
  map<int, multimap<double, int>> family;
  size_t indexed = 0;
  map<TypeKey, TypeKey> reused;
  target_cost = [&](const TypeKey &key) {
    auto found = game.ids.find(key);
    if (found == game.ids.end())
      return 2;
    return game.entries[found->second].status == Game::Local ? 0 : 1;
  };
  reuse_target = [&](const TypeKey &key) {
    if (game.ids.count(key))
      return key;
    auto found = reused.find(key);
    if (found != reused.end() &&
        game.entries[game.ids.at(found->second)].status == Game::Local) {
      ++reused_targets;
      return found->second;
    }
    auto [cid, a, b] = key;
    const auto &c = cells[cid];
    TypeKey selected = key;
    double wanted_lo = val(c, c.pool[a]), wanted_hi = val(c, c.pool[b]);
    auto &widths = family[cid];
    for (auto it = widths.lower_bound(wanted_hi - wanted_lo - 1e-12);
         it != widths.end(); ++it) {
      int i = it->second;
      const auto &entry = game.entries[i];
      if (entry.status != Game::Local)
        continue;
      ++containment_candidates;
      auto [unused, lo, hi] = entry.key;
      if (val(c, c.pool[lo]) <= wanted_lo + 1e-12 &&
          wanted_hi <= val(c, c.pool[hi]) + 1e-12 &&
          ge(c, c.pool[a], c.pool[lo]) && ge(c, c.pool[hi], c.pool[b])) {
        selected = entry.key;
        break;
      }
    }
    if (selected != key) {
      reused[key] = selected;
      ++reused_targets;
    } else if (found != reused.end())
      reused.erase(found);
    return selected;
  };
  Game::Planner planner = [&](const TypeKey &key,
                              const function<bool(const TypeKey &)> &dead) {
    check_time();
    while (indexed < game.entries.size()) {
      auto [cid, lo, hi] = game.entries[indexed].key;
      const auto &c = cells[cid];
      family[cid].emplace(val(c, c.pool[hi]) - val(c, c.pool[lo]), indexed);
      ++indexed;
    }
    if (game.steps % 500 == 0) {
      cerr << "lazy steps " << game.steps << " types " << game.entries.size()
           << " cells " << cells.size() << " expanded " << expanded_cells
           << " rejected " << game.rejected << " seeds " << tried_roots << '\n';
      lazy_snapshot(output, game, node_limit, false);
    }
    if (!lazy_available(key) ||
        (planner_mode == "dyadic" && dominated_type(key)))
      return optional<Game::Proposal>{};
    // The offer's endpoint mask has ALREADY intersected the membership
    // constraints of every destination. Rechecking millions of endpoint
    // pairs here is redundant; only newly learned failed types can differ.
    if (planner_mode == "dyadic") {
      auto unavailable = [&](const TypeKey &child) {
        return dead(child) || dominated_type(child);
      };
      auto result = dyadic_plan(key, unavailable);
      if (!result)
        learn_failed_interval(key);
      return result;
    }
    return plan_cover(key, target_bank(key), dead);
  };
  try {
    for (int trial = 0; trial < min(root_trials, int(seeds.size())); ++trial) {
      if (trial)
        game.start_root(seeds[trial]);
      ++tried_roots;
      game.run(planner, node_limit, game.steps + root_step_budget);
      lazy_snapshot(output, game, node_limit, false);
      if (game.closed) {
        stop_reason = "closed candidate requires exact replay";
        break;
      }
      if (game.node_limit_reached) {
        stop_reason = "registered type limit";
        break;
      }
    }
  } catch (const SearchLimit &error) {
    stop_reason = error.what();
  }
  if (!game.closed) {
    for (int i : game.supported_nodes())
      if (get<0>(game.entries[i].key) == root) {
        game.start_root(game.entries[i].key);
        game.closed = game.closure();
        if (game.closed) {
          stop_reason = "closed cached component requires exact replay";
          break;
        }
      }
  }
  lazy_snapshot(output, game, node_limit, true);
  auto graph = export_game(game);
  cerr << "finished: " << stop_reason << "; " << game.entries.size()
       << " types, " << cells.size() << " cells, " << graph.nodes.size()
       << " reached, " << graph.open << " open; closed=" << game.closed << '\n';
}
#endif
