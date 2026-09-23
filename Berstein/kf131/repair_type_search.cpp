// Discover a closed interval-type graph with immutable types and automatic
// back-propagation of unsuccessful child obligations. Float discovery only.
// Usage: engine MENU MEMORY BINS BASE MAX_STEP ROUNDS OUTPUT NODES VARIANTS
//               [POOL [GRID_POWER [ROOT_FRACTION]]]
#define KF131_SEARCH_LIBRARY
#include "adaptive_type_search.cpp"
#include "finite_cover_game.hpp"
#include <cstdio>

using TypeKey = tuple<int, int, int>; // parameter cell, lower, upper
#include "outer_type_filter.hpp"
struct RepairEdge {
  Offer offer;
  vector<pair<TypeKey, bool>> targets;
  int cost = 0;
};
using RepairPlan = vector<RepairEdge>;
using Game = FiniteCoverGame<TypeKey, RepairPlan>;
int variants = 4;
int root_trials = 1, tried_roots = 0;
long root_step_budget = 0;
string strategy = "bfs";
function<TypeKey(const TypeKey &)> reuse_target = [](const TypeKey &key) {
  return key;
};
function<int(const TypeKey &)> target_cost = [](const TypeKey &) { return 0; };
long expanded_contacts = 0;
// The rejected set only grows. A contact that cannot reach a given upper
// end can never become viable later in this run. Share this information
// between types with different lower ends, without excluding other ends.
map<pair<int, int>, set<pair<double, double>>> failed_contacts;

vector<RepairEdge>
alternatives(const Cell &c, Pt current, Pt end, const vector<Offer> &bank,
             const function<bool(const TypeKey &)> &rejected) {
  vector<RepairEdge> out;
  for (const auto &old : bank) {
    if (!ge(c, current, old.lo) || !ge(c, old.hi, current))
      continue;
    const auto &m = c.moves[old.move];
    struct Choice {
      int index;
      double value;
      bool reaches;
    };
    vector<Choice> lows, highs;
    double current_value = val(c, current);
    for (int block = 0; block < (int)old.allowed.size(); ++block) {
      uint64_t remaining = old.allowed[block];
      while (remaining) {
        int i = 64 * block + __builtin_ctzll(remaining);
        remaining &= remaining - 1;
        Pt z = (*m.mapped)[i];
        double value = val(c, z);
        if (ge(c, current, z))
          lows.push_back({i, value, false});
        if (value > current_value + 1e-12 && ge(c, z, current))
          highs.push_back({i, value, ge(c, z, end)});
      }
    }
    sort(lows.begin(), lows.end(),
         [&](Choice a, Choice b) { return a.value > b.value; });
    // Reach the requested end with the least excess; otherwise maximize
    // progress. Keep several choices because their children differ.
    sort(highs.begin(), highs.end(), [&](Choice a, Choice b) {
      if (a.reaches != b.reaches)
        return a.reaches;
      return a.reaches ? a.value < b.value : a.value > b.value;
    });
    if ((int)lows.size() > variants)
      lows.resize(variants);
    if ((int)highs.size() > variants)
      highs.resize(variants);
    int nx = sides[m.sl].size(), ny = sides[m.sr].size();
    for (auto low : lows)
      for (auto high : highs) {
        int a = low.index, b = high.index;
        RepairEdge e;
        e.offer = old;
        e.offer.a = a;
        e.offer.b = b;
        e.offer.lo = (*m.mapped)[a];
        e.offer.hi = (*m.mapped)[b];
        bool ok = true;
        for (auto dep : m.deps) {
          int ia = dep.swap ? (a % ny) * nx + a / ny : a;
          int ib = dep.swap ? (b % ny) * nx + b / ny : b;
          const auto &d = cells[dep.cell];
          if (!ge(d, d.pool[ib], d.pool[ia])) {
            if (!ge(d, d.pool[ia], d.pool[ib])) {
              ok = false;
              break;
            }
            swap(ia, ib);
          }
          TypeKey key{dep.cell, ia, ib};
          if (rejected(key)) {
            ok = false;
            break;
          }
          key = reuse_target(key);
          e.cost += target_cost(key);
          e.targets.push_back({key, dep.swap});
        }
        if (ok)
          out.push_back(move(e));
      }
  }
  sort(out.begin(), out.end(), [&](const RepairEdge &a, const RepairEdge &b) {
    if (strategy == "dfs-reuse" && a.cost != b.cost)
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
plan_cover(const TypeKey &key, const vector<Offer> &bank,
           const function<bool(const TypeKey &)> &rejected) {
  auto [cid, lo, hi] = key;
  const auto &c = cells[cid];
  Pt end = c.pool[hi];
  RepairPlan plan;
  // Search contact paths as well as child choices. Memoizing unsuccessful
  // contact points prevents exponential revisiting within a single replan.
  auto &failed = failed_contacts[{cid, hi}];
  function<bool(Pt)> visit = [&](Pt current) {
    if (ge(c, current, end))
      return true;
    auto location = make_pair(current.x, current.y);
    if (failed.count(location))
      return false;
    ++expanded_contacts;
    for (auto &edge : alternatives(c, current, end, bank, rejected)) {
      plan.push_back(edge);
      if (visit(edge.offer.hi))
        return true;
      plan.pop_back();
    }
    failed.insert(location);
    return false;
  };
  if (!visit(c.pool[lo]))
    return nullopt;
  Game::Proposal result;
  result.plan = move(plan);
  for (const auto &e : result.plan)
    for (const auto &target : e.targets)
      result.children.push_back(target.first);
  return result;
}

Graph export_game(const Game &game) {
  Graph out;
  auto reached = game.reachable();
  map<int, int> renumber;
  for (int i = 0; i < (int)reached.size(); ++i)
    renumber[reached[i]] = i;
  for (int i : reached) {
    const auto &entry = game.entries[i];
    auto [cid, lo, hi] = entry.key;
    Node node{cid, lo, hi, entry.status == Game::Local, {}};
    for (const auto &e : entry.plan) {
      Edge edge;
      edge.offer = e.offer;
      for (const auto &target : e.targets)
        edge.targets.push_back(
            {renumber.at(game.ids.at(target.first)), target.second});
      node.edges.push_back(move(edge));
    }
    out.open += !node.covered;
    out.nodes.push_back(move(node));
  }
  out.closed = game.closed;
  out.processed_tasks = game.steps;
  out.queued_tasks = game.scheduled;
  return out;
}

void snapshot(const string &output, const Game &game,
              const vector<array<long, 7>> &history, int node_limit,
              double root_fraction, bool finished) {
  auto graph = export_game(game);
  save(output + ".tmp", graph, history);
  if (rename((output + ".tmp").c_str(), output.c_str()) != 0)
    throw runtime_error("could not install graph checkpoint");
  string sidecar = output + ".search.json";
  ofstream report(sidecar + ".tmp");
  report << "{\"registered_types\":" << game.entries.size()
         << ",\"rejected_types\":" << game.rejected
         << ",\"parent_replans\":" << game.replans
         << ",\"processed_tasks\":" << game.steps
         << ",\"scheduled_tasks\":" << game.scheduled
         << ",\"cancelled_tasks\":" << game.cancelled
         << ",\"expanded_contacts\":" << expanded_contacts
         << ",\"outer_queries\":" << outer_queries
         << ",\"outer_rejections\":" << outer_rejections
         << ",\"outer_sample_unions\":" << outer_cache.size()
         << ",\"outer_refinements\":" << outer_refinements
         << ",\"reachable_types\":" << graph.nodes.size()
         << ",\"open_types\":" << graph.open
         << ",\"closed_candidate\":" << (game.closed ? "true" : "false")
         << ",\"limit_reached\":" << (game.limit_reached ? "true" : "false")
         << ",\"node_limit_reached\":"
         << (game.node_limit_reached ? "true" : "false")
         << ",\"finished\":" << (finished ? "true" : "false")
         << ",\"root_rejected\":"
         << (game.entries[game.root_id].status == Game::Rejected ? "true"
                                                                 : "false")
         << ",\"root_trials\":" << root_trials
         << ",\"tried_roots\":" << tried_roots
         << ",\"root_step_budget\":" << root_step_budget
         << ",\"node_limit\":" << node_limit << ",\"variants\":" << variants
         << ",\"strategy\":\"" << strategy << "\""
         << ",\"outer_depth\":" << outer_depth
         << ",\"outer_samples\":" << outer_samples
         << ",\"outer_max_depth\":" << outer_max_depth
         << ",\"root_fraction\":" << root_fraction << "}\n";
  report.close();
  if (rename((sidecar + ".tmp").c_str(), sidecar.c_str()) != 0)
    throw runtime_error("could not install search checkpoint");
}

#ifndef KF131_REPAIR_LIBRARY
int main(int argc, char **argv) {
  if (argc < 10) {
    cerr << "usage: engine MENU MEMORY BINS BASE MAX_STEP ROUNDS OUTPUT "
            "NODES VARIANTS [POOL [GRID_POWER [ROOT_FRACTION]]]\n";
    return 2;
  }
  menu = stoi(argv[1]);
  memory = stoi(argv[2]);
  bins = stoi(argv[3]);
  base = stod(argv[4]);
  maxstep = stoi(argv[5]);
  int rounds = stoi(argv[6]);
  string output = argv[7];
  int node_limit = stoi(argv[8]);
  variants = stoi(argv[9]);
  pool_mode = argc > 10 ? argv[10] : "extrema";
  grid_power = argc > 11 ? stoi(argv[11]) : 4;
  double root_fraction = argc > 12 ? stod(argv[12]) : 1.;
  strategy = argc > 13 ? argv[13] : "bfs";
  outer_depth = argc > 14 ? stoi(argv[14]) : 0;
  outer_samples = argc > 15 ? stoi(argv[15]) : 3;
  outer_max_depth = argc > 16 ? stoi(argv[16]) : outer_depth;
  root_trials = argc > 17 ? stoi(argv[17]) : 1;
  root_step_budget = argc > 18 ? stol(argv[18]) : 0;
  if (menu < 1 || memory < 1 || bins < 1 || base <= 0 || base >= 1 ||
      maxstep < 1 || rounds < 0 || node_limit < 1 || variants < 1 ||
      grid_power < 1 || grid_power > 10 || root_fraction <= 0 ||
      root_fraction > 1 || root_trials < 1 || root_step_budget < 0 ||
      outer_depth < 0 || outer_depth > 8 || outer_max_depth < outer_depth ||
      outer_max_depth > 8 ||
      (outer_samples != 1 && outer_samples != 3 && outer_samples != 11) ||
      (strategy != "bfs" && strategy != "dfs" && strategy != "dfs-reuse") ||
      (pool_mode != "grid" && pool_mode != "mixed" && pool_mode != "extrema"))
    return 2;
  root_left = "112" + string(memory, '2');
  root_right = "122" + string(memory, '2');
  prepare();
  prepare_outer_filter();
  int root = -1;
  for (int i = 0; i < (int)cells.size(); ++i) {
    const auto &c = cells[i];
    if (shapes[c.s].word == string(memory, '2') &&
        shapes[c.t].word == string(memory, '2') && c.p == 1 && c.q.lo <= .5 &&
        .5 <= c.q.hi)
      root = i;
  }
  vector<array<long, 7>> history;
  for (int n = 0; n < rounds; ++n) {
    auto all = memberships();
    vector<vector<pair<int, int>>> next;
    long active = 0, components = 0, changed = 0;
    for (auto &c : cells) {
      auto d = update(c, offers(c, all));
      active += !d.empty();
      components += d.size();
      changed += d != c.dom;
      next.push_back(move(d));
    }
    for (int i = 0; i < (int)cells.size(); ++i)
      cells[i].dom = move(next[i]);
    history.push_back(
        {n, active, components, changed, long(cells[root].dom.size()), 0, 0});
    cerr << "bank round " << n << " components " << components << endl;
  }
  auto mem = memberships();
  map<int, vector<Offer>> banks;
  banks[root] = offers(cells[root], mem);
  auto initial = update(cells[root], banks[root]);
  if (initial.empty()) {
    save(output, Graph{}, history);
    return 0;
  }
  auto &rc = cells[root];
  auto width = [&](pair<int, int> ab) {
    return val(rc, rc.pool[ab.second]) - val(rc, rc.pool[ab.first]);
  };
  auto seed = *max_element(initial.begin(), initial.end(),
                           [&](auto a, auto b) { return width(a) < width(b); });
  if (root_fraction < 1) {
    double middle =
        (val(rc, rc.pool[seed.first]) + val(rc, rc.pool[seed.second])) / 2;
    double half = root_fraction * width(seed) / 2;
    int lo = -1, hi = -1;
    for (int i : rc.order)
      if (val(rc, rc.pool[i]) >= middle - half &&
          val(rc, rc.pool[i]) <= middle + half &&
          ge(rc, rc.pool[i], rc.pool[seed.first]) &&
          ge(rc, rc.pool[seed.second], rc.pool[i])) {
        if (lo < 0)
          lo = i;
        if (ge(rc, rc.pool[i], rc.pool[lo]))
          hi = i;
      }
    if (lo >= 0 && hi >= 0 && hi != lo)
      seed = {lo, hi};
  }
  // Before growing the graph, avoid a root that already crosses a gap in a
  // finite outer union. Choose a narrower uniformly ordered interval from
  // the same endpoint menu, without changing its parameter box.
  if (!outer_possible({root, seed.first, seed.second})) {
    auto original = seed;
    double widest = -1;
    vector<int> eligible;
    for (int a : rc.order)
      if (ge(rc, rc.pool[a], rc.pool[original.first]) &&
          ge(rc, rc.pool[original.second], rc.pool[a]))
        eligible.push_back(a);
    for (int a : eligible)
      for (int b : eligible) {
        double w = val(rc, rc.pool[b]) - val(rc, rc.pool[a]);
        if (w <= widest || w <= 1e-12 ||
            !ge(rc, rc.pool[original.second], rc.pool[b]) ||
            !ge(rc, rc.pool[b], rc.pool[a]))
          continue;
        if (outer_possible({root, a, b})) {
          widest = w;
          seed = {a, b};
        }
      }
  }
  Game game({root, seed.first, seed.second}, strategy != "bfs");
  vector<vector<int>> family(cells.size());
  size_t indexed = 0;
  map<TypeKey, TypeKey> reused;
  if (strategy == "dfs-reuse") {
    target_cost = [&](const TypeKey &key) {
      auto it = game.ids.find(key);
      if (it == game.ids.end())
        return 2;
      return game.entries[it->second].status == Game::Local ? 0 : 1;
    };
    reuse_target = [&](const TypeKey &key) {
      if (game.ids.count(key))
        return key;
      auto cached = reused.find(key);
      if (cached != reused.end())
        return cached->second;
      auto [cid, a, b] = key;
      const auto &c = cells[cid];
      TypeKey selected = key;
      double width = 1e99;
      for (int i : family[cid]) {
        const auto &entry = game.entries[i];
        if (entry.status != Game::Local)
          continue;
        int lo = get<1>(entry.key), hi = get<2>(entry.key);
        double w = val(c, c.pool[hi]) - val(c, c.pool[lo]);
        if (w < width && ge(c, c.pool[a], c.pool[lo]) &&
            ge(c, c.pool[hi], c.pool[b])) {
          selected = entry.key;
          width = w;
        }
      }
      reused[key] = selected;
      return selected;
    };
  }
  Game::Planner planner = [&](const TypeKey &key,
                              const function<bool(const TypeKey &)> &rejected) {
    while (indexed < game.entries.size()) {
      family[get<0>(game.entries[indexed].key)].push_back(indexed);
      ++indexed;
    }
    reused.clear();
    int cid = get<0>(key);
    long attempts = game.entries[game.ids.at(key)].attempts;
    if (attempts >= 128 && !(attempts & (attempts - 1)))
      refine_outer_filter(cid);
    if (!banks.count(cid))
      banks[cid] = offers(cells[cid], mem);
    if (game.steps % 1000 == 0) {
      cerr << "repair steps " << game.steps << " types " << game.entries.size()
           << " rejected " << game.rejected << " replans " << game.replans
           << endl;
      snapshot(output, game, history, node_limit, root_fraction, false);
    }
    if (!outer_possible(key))
      return optional<Game::Proposal>{};
    auto unavailable = [&](const TypeKey &child) {
      return rejected(child) || !outer_possible(child);
    };
    return plan_cover(key, banks[cid], unavailable);
  };
  vector<TypeKey> seeds{{root, seed.first, seed.second}};
  for (size_t trial = 0; trial < seeds.size() && tried_roots < root_trials;
       ++trial) {
    if (trial)
      game.start_root(seeds[trial]);
    ++tried_roots;
    long limit = root_step_budget
                     ? min(20L * node_limit, game.steps + root_step_budget)
                     : 20L * node_limit;
    game.run(planner, node_limit, limit);
    snapshot(output, game, history, node_limit, root_fraction, false);
    if (game.closed || game.node_limit_reached ||
        game.steps >= 20L * node_limit)
      break;
    if (trial == 0 && root_trials > 1) {
      // Interior existence allows another small seed interval in the same
      // physical parent. Keep learned failed types while changing the seed.
      set<TypeKey> candidates;
      for (auto ab : initial) {
        Bits mask = range_mask(rc, rc.pool[ab.first], rc.pool[ab.second]);
        vector<int> allowed;
        for (int a : rc.order)
          if (mask[a / 64] & (1ULL << (a % 64)))
            allowed.push_back(a);
        for (int i = 0; i < (int)allowed.size(); ++i) {
          int accepted = 0, a = allowed[i];
          for (int j = i + 1; j < (int)allowed.size() && accepted < 2; ++j) {
            int b = allowed[j];
            TypeKey key{root, a, b};
            if (val(rc, rc.pool[b]) <= val(rc, rc.pool[a]) + 1e-11 ||
                !ge(rc, rc.pool[b], rc.pool[a]) || !outer_possible(key))
              continue;
            candidates.insert(key);
            ++accepted;
          }
        }
      }
      vector<TypeKey> extra(candidates.begin(), candidates.end());
      double center = val(rc, {anchor, anchor});
      auto distance = [&](const TypeKey &key) {
        return abs(
            (val(rc, rc.pool[get<1>(key)]) + val(rc, rc.pool[get<2>(key)])) /
                2 -
            center);
      };
      sort(extra.begin(), extra.end(),
           [&](auto a, auto b) { return distance(a) < distance(b); });
      for (const auto &key : extra)
        if (key != seeds[0])
          seeds.push_back(key);
      cerr << "prepared " << seeds.size() << " alternative seed intervals\n";
    }
  }
  if (!game.closed) {
    auto supported = game.supported_nodes();
    for (int i : supported)
      if (get<0>(game.entries[i].key) == root) {
        game.start_root(game.entries[i].key);
        game.closed = game.closure();
        if (game.closed)
          break;
      }
  }
  auto graph = export_game(game);
  snapshot(output, game, history, node_limit, root_fraction, true);
  cerr << "finished: " << game.entries.size() << " registered, " << game.replans
       << " parent replans; " << graph.nodes.size() << " reachable, "
       << graph.open << " open; closed=" << game.closed << endl;
}
#endif
