// Fixed scalar atoms, built only when requested by a predecessor. A child
// interval may be covered by several adjacent atoms for each parameter box.
#define KF131_LAZY_LIBRARY
#include "lazy_type_search.cpp"
#include <limits>

using Atom = pair<int, int>; // parameter cell, scalar grid bin
struct AtlasCase {
  bool swap;
  int lo, hi;
  vector<Atom> targets;
};
struct AtlasPlan {
  int move = -1;
  vector<AtlasCase> cases;
};
using AtlasGame = FiniteCoverGame<Atom, AtlasPlan>;
int atlas_grid = 2048;
int box_penalty = 64;
int entry_depth = 0, entry_samples = 1;
long deep_rejections = 0;
map<Atom, bool> deep_possible;
long atlas_queries = 0, atlas_rejections = 0;
map<Atom, bool> atlas_possible;
map<CellKey, int> virtual_ids;
vector<CellKey> virtual_boxes;
set<int> atlas_active_cells;
size_t atlas_indexed = 0;
int virtual_cell(int s, int t, int p, int q) {
  CellKey key{s, t, p, q};
  auto existing = lazy_ids.find(key);
  if (existing != lazy_ids.end())
    return existing->second;
  auto old = virtual_ids.find(key);
  if (old != virtual_ids.end())
    return old->second;
  int id = -1 - int(virtual_boxes.size());
  virtual_boxes.push_back(key);
  virtual_ids[key] = id;
  return id;
}
int peek_cell(int id) {
  if (id >= 0)
    return id;
  auto found = lazy_ids.find(virtual_boxes[-1 - id]);
  return found == lazy_ids.end() ? id : found->second;
}
int materialize_cell(int id) {
  if (id >= 0)
    return id;
  auto [s, t, p, q] = virtual_boxes[-1 - id];
  return lazy_cell(s, t, p, q);
}
void atlas_moves(int cid) {
  if (moves_ready[cid])
    return;
  check_time();
  prepare_moves(cells[cid], virtual_cell);
  moves_ready[cid] = true;
  ++expanded_cells;
  created_moves += cells[cid].moves.size();
}
bool atom_available(Atom key);
optional<Atom> choose_atom(int descriptor, int k,
                           const function<bool(const Atom &)> &dead,
                           bool geometry) {
  CellKey original = descriptor >= 0
                         ? CellKey{cells[descriptor].s, cells[descriptor].t,
                                   cells[descriptor].p, cells[descriptor].qi}
                         : virtual_boxes[-1 - descriptor];
  auto [si, ti, p, q] = original;
  string left = shapes[si].word, right = shapes[ti].word;
  int last = max(left.size(), right.size()),
      first = minimum_shape_memory ? minimum_shape_memory : last;
  for (int level = first; level <= last; ++level) {
    int ls = shape_lookup.at(
        left.substr(left.size() - min(int(left.size()), level)));
    int rs = shape_lookup.at(
        right.substr(right.size() - min(int(right.size()), level)));
    int cid = peek_cell(virtual_cell(ls, rs, p, q));
    if (cid >= 0) {
      if (dead({cid, k}))
        continue;
      auto known = atlas_possible.find({cid, k});
      if (known != atlas_possible.end() && !known->second)
        continue;
    }
    if (geometry) {
      cid = materialize_cell(cid);
      if (!atom_available({cid, k}))
        continue;
    }
    return Atom{cid, k};
  }
  return nullopt;
}

Bounds atlas_shift(string word, Bounds shape) {
  double z = phi(word, anchor);
  if (word.find_first_not_of('2') == string::npos)
    z = anchor;
  auto f = [&](double r) {
    return (z - anchor) * (1 + r * anchor) / (1 + r * z);
  };
  return {min(f(shape.lo), f(shape.hi)), max(f(shape.lo), f(shape.hi))};
}
Bounds atlas_gain(string word, Bounds shape) {
  auto matrix = mat(word);
  auto f = [&](double r) {
    double v = ((matrix[2] * anchor + matrix[3]) +
                r * (matrix[0] * anchor + matrix[1])) /
               (1 + r * anchor);
    return 1 / (v * v);
  };
  return {min(f(shape.lo), f(shape.hi)), max(f(shape.lo), f(shape.hi))};
}
pair<int, int> atlas_preimage_interval(const Cell &c, const Move &m, bool sw,
                                       double first, double last) {
  auto left = atlas_shift(m.u, c.r), right = atlas_shift(m.v, c.sb);
  if (c.p < 0)
    right = {-right.hi, -right.lo};
  Bounds shift{left.lo + min(c.q.lo * right.lo, c.q.hi * right.lo),
               left.hi + max(c.q.lo * right.hi, c.q.hi * right.hi)};
  Bounds gain = atlas_gain(sw ? m.v : m.u, sw ? c.sb : c.r);
  int sign = (sw ? c.p : 1) * ((sw ? m.v : m.u).size() % 2 ? -1 : 1);
  if (sw)
    gain = {gain.lo * c.q.lo, gain.hi * c.q.hi};
  if (sign < 0)
    gain = {-gain.hi, -gain.lo};
  double low = 1e99, high = -1e99;
  for (double t : {double(first) / atlas_grid, double(last) / atlas_grid})
    for (double shift_value : {shift.lo, shift.hi})
      for (double gain_value : {gain.lo, gain.hi}) {
        double x = (t - shift_value) / gain_value;
        low = min(low, x);
        high = max(high, x);
      }
  // Near-grid rounding can only propose a candidate. The exact core-image
  // check must still verify the complete parent interval before acceptance.
  if (!(low >= -4 && high <= 4))
    return {0, 129};
  return {int(floor(low * atlas_grid + 1e-10)),
          int(ceil(high * atlas_grid - 1e-10))};
}
pair<int, int> atlas_preimage(const Cell &c, const Move &m, bool sw, int atom) {
  return atlas_preimage_interval(c, m, sw, atom, atom + 1);
}
double centered_min(const Cell &c, Pt a, Pt b) {
  double x = delta_min(a.x, b.x, c.r);
  double y = c.p > 0 ? delta_min(a.y, b.y, c.sb) : delta_min(b.y, a.y, c.sb);
  return x + (y >= 0 ? c.q.lo : c.q.hi) * y;
}
bool atom_available(Atom key) {
  auto found = atlas_possible.find(key);
  if (found != atlas_possible.end())
    return found->second;
  ++atlas_queries;
  int cid = key.first, k = key.second;
  const auto &c = cells[cid];
  double a = (2 * sqrt(10) - 5) / 5, b = (2 * sqrt(10) - 4) / 3,
         cc = (sqrt(10) - 2) / 4, d = (2 * sqrt(10) - 5) / 3;
  array<Bounds, 3> hulls = {Bounds{a, b}, Bounds{cc, b}, Bounds{a, d}};
  auto l = hulls[shapes[c.s].state], r = hulls[shapes[c.t].state];
  Pt low{l.lo, c.p > 0 ? r.lo : r.hi}, high{l.hi, c.p > 0 ? r.hi : r.lo},
      zero{anchor, anchor};
  double lo = double(k) / atlas_grid, hi = double(k + 1) / atlas_grid;
  bool valid = lo >= -centered_min(c, zero, low) - 1e-12 &&
               hi <= centered_min(c, high, zero) + 1e-12;
  if (valid)
    for (int sample = 0; sample < membership_samples; ++sample) {
      double origin = sample_value(c, zero, sample);
      if (!outer_contains(cid, sample, origin + lo, origin + hi)) {
        valid = false;
        break;
      }
    }
  atlas_rejections += !valid;
  atlas_possible[key] = valid;
  return valid;
}
bool atom_entry_check(Atom key) {
  if (entry_depth <= outer_depth)
    return true;
  auto found = deep_possible.find(key);
  if (found != deep_possible.end())
    return found->second;
  int cid = key.first, old_depth = outer_cell_depth[cid];
  outer_cell_depth[cid] = entry_depth;
  const auto &c = cells[cid];
  bool possible = true;
  for (int sample = 0; sample < entry_samples; ++sample) {
    double center = sample_value(c, {anchor, anchor}, sample);
    if (!outer_contains(cid, sample, center + double(key.second) / atlas_grid,
                        center + double(key.second + 1) / atlas_grid)) {
      possible = false;
      break;
    }
  }
  outer_cell_depth[cid] = old_depth;
  deep_rejections += !possible;
  deep_possible[key] = possible;
  return possible;
}
void atlas_save(const string &output, const AtlasGame &game, bool finished) {
  auto reached = game.reachable();
  map<int, int> index;
  for (int i = 0; i < int(reached.size()); ++i)
    index[reached[i]] = i;
  int open = 0;
  for (int i : reached)
    open += game.entries[i].status != AtlasGame::Local;
  ofstream out(output + ".tmp");
  out << setprecision(17);
  out << "{\"schema\":\"kf131-scalar-atlas-v1\",\"settings\":{\"base\":" << base
      << ",\"bins\":" << bins << ",\"memory\":" << memory
      << ",\"grid\":" << atlas_grid << ",\"max_step\":" << maxstep
      << "},\"root_prefixes\":[\"" << root_left << "\",\"" << root_right
      << "\"],\"roots\":[0],\"closed_candidate\":"
      << (game.closed ? "true" : "false") << ",\"open_nodes\":" << open
      << ",\"processed_tasks\":" << game.steps
      << ",\"queued_tasks\":" << game.scheduled << ",\"nodes\":[";
  for (int ni = 0; ni < int(reached.size()); ++ni) {
    if (ni)
      out << ',';
    const auto &e = game.entries[reached[ni]];
    const auto &c = cells[e.key.first];
    out << "{\"id\":" << ni << ",\"states\":[\"" << shapes[c.s].word << "\",\""
        << shapes[c.t].word << "\"],\"parity\":" << c.p
        << ",\"ratio_bin\":" << c.qi << ",\"interval\":[" << e.key.second << ','
        << e.key.second + 1
        << "],\"covered\":" << (e.status == AtlasGame::Local ? "true" : "false")
        << ",\"children\":[";
    if (e.status == AtlasGame::Local) {
      const auto &m = c.moves[e.plan.move];
      out << "{\"suffixes\":[\"" << m.u << "\",\"" << m.v << "\"],\"cases\":[";
      for (int k = 0; k < int(e.plan.cases.size()); ++k) {
        if (k)
          out << ',';
        const auto &q = e.plan.cases[k];
        out << "{\"swap\":" << (q.swap ? "true" : "false") << ",\"interval\":["
            << q.lo << ',' << q.hi << "],\"destinations\":[";
        for (int j = 0; j < int(q.targets.size()); ++j) {
          if (j)
            out << ',';
          out << index.at(game.ids.at(q.targets[j]));
        }
        out << "]}";
      }
      out << "]}";
    }
    out << "]}";
  }
  out << "]}\n";
  out.close();
  rename((output + ".tmp").c_str(), output.c_str());
  ofstream log(output + ".lazy.json.tmp");
  log << "{\"registered_types\":" << game.entries.size()
      << ",\"rejected_types\":" << game.rejected
      << ",\"parent_replans\":" << game.replans
      << ",\"processed_tasks\":" << game.steps
      << ",\"parameter_cells\":" << cells.size()
      << ",\"expanded_cells\":" << expanded_cells
      << ",\"virtual_parameter_cells\":" << virtual_boxes.size()
      << ",\"active_parameter_cells\":" << atlas_active_cells.size()
      << ",\"box_penalty\":" << box_penalty
      << ",\"minimum_shape_memory\":" << minimum_shape_memory
      << ",\"entry_depth\":" << entry_depth
      << ",\"entry_samples\":" << entry_samples
      << ",\"deep_queries\":" << deep_possible.size()
      << ",\"deep_rejections\":" << deep_rejections
      << ",\"outer_unions\":" << outer_cache.size()
      << ",\"atom_queries\":" << atlas_queries
      << ",\"atom_rejections\":" << atlas_rejections
      << ",\"tried_roots\":" << tried_roots
      << ",\"reachable_types\":" << reached.size() << ",\"open_types\":" << open
      << ",\"elapsed_seconds\":" << elapsed() << ",\"stop\":\"" << stop_reason
      << "\",\"finished\":" << (finished ? "true" : "false") << "}\n";
  log.close();
  rename((output + ".lazy.json.tmp").c_str(), (output + ".lazy.json").c_str());
}
#ifndef KF131_ATLAS_LIBRARY
int main(int argc, char **argv) {
  if (argc < 20) {
    cerr << "use lazy_type_search.py --method atlas\n";
    return 2;
  }
  menu = 1;
  memory = stoi(argv[2]);
  bins = stoi(argv[3]);
  base = stod(argv[4]);
  maxstep = stoi(argv[5]);
  string output = argv[6];
  int node_limit = stoi(argv[7]);
  outer_depth = stoi(argv[9]);
  membership_samples = stoi(argv[10]);
  root_trials = stoi(argv[12]);
  root_step_budget = stol(argv[13]);
  max_cells = stoi(argv[14]);
  seconds_limit = stod(argv[15]);
  atlas_grid = stoi(argv[19]);
  box_penalty = argc > 20 ? stoi(argv[20]) : 64;
  minimum_shape_memory = argc > 21 ? stoi(argv[21]) : 0;
  entry_depth = argc > 22 ? stoi(argv[22]) : outer_depth;
  entry_samples = argc > 23 ? stoi(argv[23]) : 1;
  if (memory < 1 || memory > 8 || bins < 1 || base <= 0 || base >= 1 ||
      maxstep < 1 || maxstep > 6 || outer_depth < 1 || outer_depth > 7 ||
      (membership_samples != 1 && membership_samples != 3 &&
       membership_samples != 11) ||
      atlas_grid < 1 || atlas_grid > 10000000 || max_cells < 1 ||
      node_limit < 1 || root_trials < 1 || root_step_budget < 1 ||
      seconds_limit <= 0 || box_penalty < 0 ||
      (minimum_shape_memory &&
       (minimum_shape_memory < 2 || minimum_shape_memory > memory)))
    return 2;
  if (entry_depth < outer_depth || entry_depth > 7 ||
      (entry_samples != 1 && entry_samples != 3 && entry_samples != 11))
    return 2;
  root_left = argc > 24 ? argv[24] : "112" + string(memory, '2');
  root_right = argc > 25 ? argv[25] : "122" + string(memory, '2');
  for (const auto &word : {root_left, root_right})
    if (word.size() <= size_t(memory) || word.size() > 64 ||
        word.find_first_not_of("123") != string::npos || state(word) < 0)
      return 2;
  auto root_weight = [](const string &word) {
    auto m = mat(word);
    return m[2] * anchor + m[3];
  };
  if (root_weight(root_left) > root_weight(root_right))
    swap(root_left, root_right);
  double root_ratio = pow(root_weight(root_left) / root_weight(root_right), 2);
  prepare_catalog();
  int ls = shape_lookup.at(root_left.substr(root_left.size() - memory)),
      rs = shape_lookup.at(root_right.substr(root_right.size() - memory)),
      qi = -1;
  for (int i = 0; i < bins; ++i)
    if (qb[i].lo <= root_ratio && root_ratio <= qb[i].hi)
      qi = i;
  if (qi < 0)
    return 2;
  int parity = (root_left.size() + root_right.size()) % 2 ? -1 : 1;
  int root = lazy_cell(ls, rs, parity, qi);
  auto lm = mat(root_left), rm = mat(root_right);
  if (!(cells[root].r.lo <= lm[2] / lm[3] &&
        lm[2] / lm[3] <= cells[root].r.hi &&
        cells[root].sb.lo <= rm[2] / rm[3] &&
        rm[2] / rm[3] <= cells[root].sb.hi))
    return 2;
  AtlasGame game({root, 0}, true);
  atlas_save(output, game, false);
  AtlasGame::Planner planner = [&](const Atom &key,
                                   const function<bool(const Atom &)> &dead)
      -> optional<AtlasGame::Proposal> {
    check_time();
    if (game.steps % 1000 == 0) {
      cerr << "atlas steps " << game.steps << " atoms " << game.entries.size()
           << " cells " << cells.size() << " rejected " << game.rejected
           << '\n';
      atlas_save(output, game, false);
    }
    if (!atom_available(key) || !atom_entry_check(key))
      return nullopt;
    while (atlas_indexed < game.entries.size())
      atlas_active_cells.insert(game.entries[atlas_indexed++].key.first);
    atlas_moves(key.first);
    const auto &c = cells[key.first];
    vector<pair<long, AtlasGame::Proposal>> candidates;
    for (int mi = 0; mi < int(c.moves.size()); ++mi) {
      check_time();
      const auto &m = c.moves[mi];
      AtlasGame::Proposal proposal;
      proposal.plan.move = mi;
      bool valid = true;
      long cost = 0;
      set<int> new_boxes;
      for (bool sw : {false, true}) {
        vector<int> deps;
        for (auto dep : m.deps)
          if (dep.swap == sw)
            deps.push_back(dep.cell);
        if (deps.empty())
          continue;
        auto bounds = atlas_preimage(c, m, sw, key.second);
        if (bounds.second <= bounds.first ||
            bounds.second - bounds.first > 128) {
          valid = false;
          break;
        }
        AtlasCase branch{sw, bounds.first, bounds.second, {}};
        for (int raw : deps) {
          for (int k = bounds.first; k < bounds.second; ++k) {
            auto estimated = choose_atom(raw, k, dead, false);
            if (!estimated) {
              valid = false;
              break;
            }
            int cid = estimated->first;
            if (cid < 0 || !atlas_active_cells.count(cid))
              new_boxes.insert(cid);
            auto found = game.ids.find(*estimated);
            cost += found == game.ids.end() ? 4
                    : game.entries[found->second].status == AtlasGame::Local
                        ? 0
                        : 1;
            branch.targets.push_back({raw, k});
            proposal.children.push_back({raw, k});
          }
          if (!valid)
            break;
        }
        if (!valid)
          break;
        proposal.plan.cases.push_back(move(branch));
      }
      if (proposal.children.empty())
        valid = false;
      cost = (cost + box_penalty * long(new_boxes.size())) * 100 +
             proposal.children.size();
      if (valid)
        candidates.push_back({cost, move(proposal)});
    }
    stable_sort(candidates.begin(), candidates.end(),
                [](const auto &a, const auto &b) { return a.first < b.first; });
    // Test only the most promising moves first. Arrival geometry for all
    // other moves remains a small symbolic descriptor until actually used.
    for (auto &candidate : candidates) {
      auto proposal = move(candidate.second);
      proposal.children.clear();
      bool valid = true;
      for (auto &branch : proposal.plan.cases) {
        for (auto &child : branch.targets) {
          auto actual = choose_atom(child.first, child.second, dead, true);
          if (!actual) {
            valid = false;
            break;
          }
          child = *actual;
          proposal.children.push_back(child);
        }
        if (!valid)
          break;
      }
      if (valid)
        return proposal;
    }
    return nullopt;
  };
  try {
    for (int trial = 0; trial < root_trials; ++trial) {
      int k = trial % 2 ? -(trial + 1) / 2 : trial / 2;
      if (trial)
        game.start_root({root, k});
      ++tried_roots;
      game.run(planner, node_limit, game.steps + root_step_budget);
      atlas_save(output, game, false);
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
  if (!game.closed)
    for (int i : game.supported_nodes())
      if (game.entries[i].key.first == root) {
        game.start_root(game.entries[i].key);
        game.closed = game.closure();
        if (game.closed)
          break;
      }
  atlas_save(output, game, true);
  cerr << "finished: " << stop_reason << "; atoms " << game.entries.size()
       << " cells " << cells.size() << " closed=" << game.closed << '\n';
}
#endif
