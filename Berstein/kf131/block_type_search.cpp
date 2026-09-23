// Interval obligations are compressed into dyadic blocks. A parent block
// can use several genuine (nonempty) successor maps; no identity split is
// accepted as an induction step. Output uses the existing exact verifier.
#define KF131_ATLAS_LIBRARY
#include "atlas_type_search.cpp"
#include "scalar_discovery_geometry.hpp"

using Block = tuple<int, int, int>; // cell, inclusive left, exclusive right
struct BlockCase {
  bool swap;
  int lo, hi;
  vector<Block> targets;
};
struct BlockEdge {
  int move;
  vector<BlockCase> cases;
  Bounds core;
};
struct BlockPlan {
  vector<BlockEdge> edges;
};
using BlockGame = FiniteCoverGame<Block, BlockPlan>;
// Empty outside the learned feedback policy; affects ordering, never validity.
function<double(const Block &)> learned_block_cost;
long weighted_slice_queries = 0, weighted_edge_queries = 0;
#include "weighted_interval_cover.hpp"
int block_span = 32;
bool tight_preimages = true;
long block_queries = 0, block_rejections = 0, block_splits = 0;
long parent_splits = 0, reused_blocks = 0;
long probe_steps = 0, probe_rejections = 0;
int probe_percent = 20;
int block_scheduler = 0;
int subgrid_depth = 0;
long subgrid_splits = 0;
bool probing = false, probe_closed = false;
map<pair<Block, bool>, bool> possible_blocks;
map<int, multimap<int, int>> existing_blocks;
size_t block_indexed = 0;
double last_checkpoint = 0;

bool block_available(Block key, bool deep) {
  auto cached = possible_blocks.find({key, deep});
  if (cached != possible_blocks.end())
    return cached->second;
  check_time();
  ++block_queries;
  auto [cid, lo, hi] = key;
  bool valid = atom_available({cid, lo}) && atom_available({cid, hi - 1});
  int previous_depth = outer_cell_depth[cid];
  if (deep)
    outer_cell_depth[cid] = entry_depth;
  int samples = deep ? entry_samples : membership_samples;
  for (int sample = 0; valid && sample < samples; ++sample) {
    double center = sample_value(cells[cid], {anchor, anchor}, sample);
    valid = outer_contains(cid, sample, center + double(lo) / atlas_grid,
                           center + double(hi) / atlas_grid);
  }
  outer_cell_depth[cid] = previous_depth;
  block_rejections += !valid;
  possible_blocks[{key, deep}] = valid;
  return valid;
}

vector<pair<int, int>> dyadic_blocks(int lo, int hi) {
  vector<pair<int, int>> parts;
  while (lo < hi) {
    int width = 1;
    while (width <= block_span / 2 && lo % (2 * width) == 0 &&
           2 * width <= hi - lo)
      width *= 2;
    parts.push_back({lo, lo + width});
    lo += width;
  }
  return parts;
}

optional<Block> containing_block(Block key, const BlockGame &game) {
  auto [cid, lo, hi] = key;
  auto found = existing_blocks.find(cid);
  if (found == existing_blocks.end())
    return nullopt;
  auto it = found->second.upper_bound(lo);
  // Reuse only locally covered types here. Pending supersets are not proof
  // and tend to make a small obligation depend on a much harder one.
  for (int budget = 128; budget && it != found->second.begin(); --budget) {
    --it;
    const auto &entry = game.entries[it->second];
    auto [c, a, b] = entry.key;
    if (b >= hi && b - a <= 4 * block_span && entry.status == BlockGame::Local)
      return entry.key;
  }
  return nullopt;
}

optional<Block> choose_whole_block(int descriptor, int lo, int hi,
                                   const function<bool(const Block &)> &dead,
                                   const BlockGame &game, bool geometry) {
  CellKey original = descriptor >= 0
                         ? CellKey{cells[descriptor].s, cells[descriptor].t,
                                   cells[descriptor].p, cells[descriptor].qi}
                         : virtual_boxes[-1 - descriptor];
  auto [si, ti, p, q] = original;
  string left = shapes[si].word, right = shapes[ti].word;
  int last = max(left.size(), right.size());
  int first = minimum_shape_memory ? minimum_shape_memory : last;
  for (int level = first; level <= last; ++level) {
    int ls = shape_lookup.at(
        left.substr(left.size() - min(int(left.size()), level)));
    int rs = shape_lookup.at(
        right.substr(right.size() - min(int(right.size()), level)));
    int cid = peek_cell(virtual_cell(ls, rs, p, q));
    Block key{cid, lo, hi};
    if (cid >= 0) {
      auto contained = containing_block(key, game);
      if (contained && !dead(*contained)) {
        if (geometry)
          ++reused_blocks;
        return contained;
      }
      auto old = possible_blocks.find({key, false});
      if (old != possible_blocks.end() && !old->second)
        continue;
    }
    if (dead(key))
      continue;
    if (geometry) {
      cid = materialize_cell(cid);
      key = {cid, lo, hi};
      if (!block_available(key, false))
        continue;
    }
    return key;
  }
  return nullopt;
}

using PieceEstimateKey = tuple<int, int, int, double, double>;
map<PieceEstimateKey, optional<vector<Block>>> piece_estimates;
long piece_estimate_hits = 0, piece_estimate_calls = 0;
bool cache_piece_estimates = true;
bool piece_estimate_scope = false;
bool choose_piece(int descriptor, int lo, int hi,
                  const function<bool(const Block &)> &dead,
                  const BlockGame &game, bool geometry, vector<Block> &out,
                  Bounds required = {0, 1});
bool choose_piece_uncached(int descriptor, int lo, int hi,
                           const function<bool(const Block &)> &dead,
                           const BlockGame &game, bool geometry,
                           vector<Block> &out, Bounds required) {
  CellKey original = descriptor >= 0
                         ? CellKey{cells[descriptor].s, cells[descriptor].t,
                                   cells[descriptor].p, cells[descriptor].qi}
                         : virtual_boxes[-1 - descriptor];
  auto [s, t, p, q] = original;
  if (ratio_clip_first && ratio_key(q).level < ratio_max_depth) {
    double middle = (qb[q].lo + qb[q].hi) / 2;
    int side = required.hi < middle - 1e-14   ? 0
               : required.lo > middle + 1e-14 ? 1
                                              : -1;
    if (side >= 0) {
      int half = ratio_half(q, side);
      if (choose_piece(virtual_cell(s, t, p, half), lo, hi, dead, game,
                       geometry, out, required)) {
        ++ratio_clipped_requests;
        return true;
      }
    }
  }
  auto whole = choose_whole_block(descriptor, lo, hi, dead, game, geometry);
  if (whole) {
    out.push_back(*whole);
    return true;
  }
  size_t before = out.size();
  if (hi - lo > 1) {
    if (geometry)
      ++block_splits;
    int mid = lo + (hi - lo) / 2;
    if (choose_piece(descriptor, lo, mid, dead, game, geometry, out,
                     required) &&
        choose_piece(descriptor, mid, hi, dead, game, geometry, out, required))
      return true;
    out.resize(before);
  }
  if (ratio_key(q).level >= ratio_max_depth)
    return false;
  ++ratio_split_attempts;
  int used = 0;
  for (int side : {0, 1}) {
    int half = ratio_half(q, side);
    Bounds part{max(required.lo, qb[half].lo), min(required.hi, qb[half].hi)};
    if (part.lo >= part.hi - 1e-14)
      continue;
    ++used;
    if (!choose_piece(virtual_cell(s, t, p, half), lo, hi, dead, game, geometry,
                      out, part)) {
      out.resize(before);
      return false;
    }
  }
  if (used)
    ++ratio_split_successes;
  return used != 0;
}
bool choose_piece(int descriptor, int lo, int hi,
                  const function<bool(const Block &)> &dead,
                  const BlockGame &game, bool geometry, vector<Block> &out,
                  Bounds required) {
  if (geometry || !cache_piece_estimates || !piece_estimate_scope)
    return choose_piece_uncached(descriptor, lo, hi, dead, game, geometry, out,
                                 required);
  ++piece_estimate_calls;
  PieceEstimateKey key{descriptor, lo, hi, required.lo, required.hi};
  auto found = piece_estimates.find(key);
  if (found == piece_estimates.end()) {
    vector<Block> value;
    bool ok = choose_piece_uncached(descriptor, lo, hi, dead, game, false,
                                    value, required);
    found =
        piece_estimates
            .emplace(key, ok ? optional<vector<Block>>(move(value)) : nullopt)
            .first;
  } else
    ++piece_estimate_hits;
  if (!found->second)
    return false;
  out.insert(out.end(), found->second->begin(), found->second->end());
  return true;
}

#include "block_known_cover.hpp"

bool direct_hull_filter = false;
long direct_hull_queries = 0, direct_hull_rejections = 0;
map<pair<int, int>, Bounds> direct_hulls;
bool move_hull_could_cover(int cid, int mi, double lo, double hi) {
  if (!direct_hull_filter)
    return true;
  ++direct_hull_queries;
  auto key = make_pair(cid, mi);
  auto found = direct_hulls.find(key);
  if (found == direct_hulls.end()) {
    const auto &c = cells[cid];
    const auto &m = c.moves[mi];
    auto shared = mapped_hulls.find(m.mapped.get());
    if (shared == mapped_hulls.end()) {
      Pt low{1, 1}, high{0, 0};
      for (auto z : *m.mapped) {
        low.x = min(low.x, z.x);
        low.y = min(low.y, z.y);
        high.x = max(high.x, z.x);
        high.y = max(high.y, z.y);
      }
      shared = mapped_hulls.emplace(m.mapped.get(), make_pair(low, high)).first;
    }
    auto low = shared->second.first, high = shared->second.second;
    if (c.p < 0)
      swap(low.y, high.y);
    Bounds common{-1e90, 1e90};
    for (int sample = 0; sample < membership_samples; ++sample) {
      double origin = sample_value(c, {anchor, anchor}, sample);
      common.lo = max(common.lo, sample_value(c, low, sample) - origin);
      common.hi = min(common.hi, sample_value(c, high, sample) - origin);
    }
    found = direct_hulls.emplace(key, common).first;
  }
  bool possible = found->second.lo <= lo / atlas_grid + 1e-11 &&
                  hi / atlas_grid <= found->second.hi + 1e-11;
  direct_hull_rejections += !possible;
  return possible;
}

optional<BlockEdge> direct_cover(int cid, double lo, double hi, BlockGame &game,
                                 const function<bool(const Block &)> &dead) {
  atlas_moves(cid);
  const auto &c = cells[cid];
  vector<pair<double, BlockEdge>> candidates;
  for (int mi = 0; mi < int(c.moves.size()); ++mi) {
    check_time();
    if (!move_hull_could_cover(cid, mi, lo, hi))
      continue;
    const auto &m = c.moves[mi];
    BlockEdge edge{mi, {}, {-1e90, 1e90}};
    bool valid = true;
    set<Block> needed;
    set<int> new_boxes;
    for (bool sw : {false, true}) {
      vector<Dep> deps;
      for (auto d : m.deps)
        if (d.swap == sw)
          deps.push_back(d);
      if (deps.empty())
        continue;
      auto bounds = discovery_preimage(c, m, sw, lo, hi, tight_preimages);
      if (bounds.second <= bounds.first ||
          bounds.second - bounds.first > 4096) {
        valid = false;
        break;
      }
      auto core = discovery_core(c, m, sw, bounds.first, bounds.second);
      edge.core.lo = max(edge.core.lo, core.lo);
      edge.core.hi = min(edge.core.hi, core.hi);
      BlockCase branch{sw, bounds.first, bounds.second, {}};
      for (const auto &dep : deps) {
        int raw = dep.cell;
        for (auto [a, b] : dyadic_blocks(bounds.first, bounds.second)) {
          vector<Block> estimate;
          if (!choose_piece(raw, a, b, dead, game, false, estimate,
                            dep.required_ratio)) {
            valid = false;
            break;
          }
          needed.insert(estimate.begin(), estimate.end());
          branch.targets.push_back({raw, a, b});
        }
        if (!valid)
          break;
      }
      if (!valid)
        break;
      edge.cases.push_back(move(branch));
    }
    if (!valid || needed.empty() ||
        edge.core.lo > double(lo) / atlas_grid + 1e-13 ||
        edge.core.hi < double(hi) / atlas_grid - 1e-13)
      continue;
    double cost = 0;
    for (const auto &key : needed) {
      int target = get<0>(key);
      if (target < 0 || !atlas_active_cells.count(target))
        new_boxes.insert(target);
      auto found = game.ids.find(key);
      cost += learned_block_cost        ? learned_block_cost(key)
              : found == game.ids.end() ? 8
              : game.entries[found->second].status == BlockGame::Local ? 0
                                                                       : 1;
    }
    cost = (cost + box_penalty * long(new_boxes.size())) * 100 + needed.size();
    candidates.push_back({cost, move(edge)});
  }
  stable_sort(candidates.begin(), candidates.end(),
              [](const auto &a, const auto &b) { return a.first < b.first; });
  for (auto &ranked : candidates) {
    BlockEdge edge = move(ranked.second);
    bool valid = true;
    for (auto &branch : edge.cases) {
      vector<Block> targets;
      for (auto [raw, a, b] : branch.targets) {
        const auto &deps = c.moves[edge.move].deps;
        int raw_id = raw;
        auto dep = find_if(deps.begin(), deps.end(), [&](const auto &d) {
          return d.cell == raw_id && d.swap == branch.swap;
        });
        if (dep == deps.end())
          throw logic_error("missing arrival range");
        if (!choose_piece(raw, a, b, dead, game, true, targets,
                          dep->required_ratio)) {
          valid = false;
          break;
        }
      }
      if (!valid)
        break;
      branch.targets = move(targets);
    }
    if (valid)
      return edge;
  }
  return nullopt;
}

bool piecewise_cover(int cid, double lo, double hi, BlockGame &game,
                     const function<bool(const Block &)> &dead,
                     vector<BlockEdge> &edges) {
  auto edge = direct_cover(cid, lo, hi, game, dead);
  if (edge) {
    edges.push_back(move(*edge));
    return true;
  }
  if (hi - lo <= ldexp(1., -subgrid_depth))
    return false;
  ++parent_splits;
  double mid = hi - lo > 1 ? lo + floor((hi - lo) / 2) : (lo + hi) / 2;
  subgrid_splits += hi - lo <= 1;
  return piecewise_cover(cid, lo, mid, game, dead, edges) &&
         piecewise_cover(cid, mid, hi, game, dead, edges);
}

optional<BlockGame::Proposal>
block_proposal(const Block &key, BlockGame &context,
               const function<bool(const Block &)> &dead) {
  struct EstimateScope {
    EstimateScope() {
      piece_estimates.clear();
      piece_estimate_scope = true;
    }
    ~EstimateScope() { piece_estimate_scope = false; }
  } estimate_scope;
  check_time();
  if (!block_available(key, false) || !block_available(key, true))
    return nullopt;
  while (block_indexed < context.entries.size()) {
    auto [c, a, b] = context.entries[block_indexed].key;
    existing_blocks[c].insert({a, block_indexed});
    atlas_active_cells.insert(c);
    ++block_indexed;
  }
  auto [cid, lo, hi] = key;
  vector<BlockEdge> candidates;
  auto known = known_cover(cid, lo, hi, context, dead);
  if (known)
    candidates = move(*known);
  else if (!piecewise_cover(cid, lo, hi, context, dead, candidates))
    return nullopt;
  BlockGame::Proposal proposal;
  auto chain = progressing_edges(candidates, double(lo) / atlas_grid,
                                 double(hi) / atlas_grid);
  if (!chain)
    return nullopt;
  proposal.plan.edges = move(*chain);
  for (const auto &edge : proposal.plan.edges) {
    for (const auto &branch : edge.cases)
      proposal.children.insert(proposal.children.end(), branch.targets.begin(),
                               branch.targets.end());
  }
  sort(proposal.children.begin(), proposal.children.end());
  proposal.children.erase(
      unique(proposal.children.begin(), proposal.children.end()),
      proposal.children.end());
  return proposal;
}

void write_block_edges(ostream &out, const BlockPlan &plan, int cid,
                       const map<int, int> &index, const BlockGame &game) {
  const auto &c = cells[cid];
  for (int ei = 0; ei < int(plan.edges.size()); ++ei) {
    if (ei)
      out << ',';
    const auto &edge = plan.edges[ei];
    const auto &m = c.moves[edge.move];
    out << "{\"suffixes\":[\"" << m.u << "\",\"" << m.v << "\"],\"cases\":[";
    for (int k = 0; k < int(edge.cases.size()); ++k) {
      if (k)
        out << ',';
      const auto &q = edge.cases[k];
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
}
function<void(ostream &, const BlockGame &, const map<int, int> &)>
    write_catalog_extra;

void block_save(const string &output, const BlockGame &game, bool finished,
                bool full_catalog = false) {
  auto reached = game.reachable();
  if (full_catalog) {
    vector<bool> seen(game.entries.size());
    for (int id : reached)
      seen[id] = true;
    for (int id = 0; id < int(seen.size()); ++id)
      if (!seen[id])
        reached.push_back(id);
  }
  map<int, int> index;
  for (int i = 0; i < int(reached.size()); ++i)
    index[reached[i]] = i;
  int open = 0, maximum_width = 0;
  long represented_atoms = 0;
  map<int, BlockDomain> distinct;
  for (int i : reached) {
    open += game.entries[i].status != BlockGame::Local;
    int width = get<2>(game.entries[i].key) - get<1>(game.entries[i].key);
    represented_atoms += width;
    maximum_width = max(maximum_width, width);
    auto [cid, lo, hi] = game.entries[i].key;
    distinct[cid].push_back({lo, hi});
  }
  long distinct_atoms = 0;
  for (auto &entry : distinct) {
    auto &parts = entry.second;
    sort(parts.begin(), parts.end());
    int covered = numeric_limits<int>::min();
    for (auto [a, b] : parts) {
      distinct_atoms += max(0, b - max(a, covered));
      covered = max(covered, b);
    }
  }
  ofstream out(output + ".tmp");
  out << setprecision(17);
  out << "{\"schema\":\"kf131-scalar-atlas-v1\",\"settings\":{\"base\":" << base
      << ",\"bins\":" << bins << ",\"memory\":" << memory
      << ",\"grid\":" << atlas_grid << ",\"max_step\":" << maxstep
      << ",\"block_span\":" << block_span << "},\"root_prefixes\":[\""
      << root_left << "\",\"" << root_right
      << "\"],\"roots\":[0],\"closed_candidate\":"
      << (game.closed ? "true" : "false") << ",\"open_nodes\":" << open
      << ",\"nodes\":[";
  for (int ni = 0; ni < int(reached.size()); ++ni) {
    if (ni)
      out << ',';
    const auto &e = game.entries[reached[ni]];
    auto [cid, a, b] = e.key;
    const auto &c = cells[cid];
    auto ratio = ratio_key(c.qi);
    out << "{\"id\":" << ni << ",\"states\":[\"" << shapes[c.s].word << "\",\""
        << shapes[c.t].word << "\"],\"parity\":" << c.p
        << ",\"ratio_bin\":" << ratio.bin;
    if (ratio.level)
      out << ",\"ratio_refinement\":[" << ratio.level << ',' << ratio.index
          << ']';
    out << ",\"interval\":[" << a << ',' << b
        << "],\"covered\":" << (e.status == BlockGame::Local ? "true" : "false")
        << ",\"children\":[";
    if (e.status == BlockGame::Local)
      write_block_edges(out, e.plan, cid, index, game);
    out << "]}";
  }
  out << ']';
  if (full_catalog && write_catalog_extra)
    write_catalog_extra(out, game, index);
  out << "}\n";
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
      << ",\"block_queries\":" << block_queries
      << ",\"block_rejections\":" << block_rejections
      << ",\"child_splits\":" << block_splits
      << ",\"parent_splits\":" << parent_splits
      << ",\"reused_blocks\":" << reused_blocks
      << ",\"represented_atoms_with_multiplicity\":" << represented_atoms
      << ",\"probe_steps\":" << probe_steps
      << ",\"probe_rejections\":" << probe_rejections
      << ",\"probe_closed\":" << (probe_closed ? "true" : "false")
      << ",\"known_cover_queries\":" << known_cover_queries
      << ",\"known_cover_successes\":" << known_cover_successes
      << ",\"represented_distinct_atoms\":" << distinct_atoms
      << ",\"scheduler\":" << block_scheduler
      << ",\"subgrid_splits\":" << subgrid_splits
      << ",\"maximum_block_width\":" << maximum_width
      << ",\"tried_roots\":" << tried_roots
      << ",\"reachable_types\":" << reached.size() << ",\"open_types\":" << open
      << ",\"elapsed_seconds\":" << elapsed() << ",\"stop\":\"" << stop_reason
      << "\",\"finished\":" << (finished ? "true" : "false") << "}\n";
  log.close();
  rename((output + ".lazy.json.tmp").c_str(), (output + ".lazy.json").c_str());
  last_checkpoint = elapsed();
}

#ifndef KF131_BLOCK_LIBRARY
int main(int argc, char **argv) {
  if (argc < 26) {
    cerr << "use lazy_type_search.py --method block\n";
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
  box_penalty = stoi(argv[20]);
  minimum_shape_memory = stoi(argv[21]);
  entry_depth = stoi(argv[22]);
  entry_samples = stoi(argv[23]);
  root_left = argv[24];
  root_right = argv[25];
  block_span = argc > 26 ? stoi(argv[26]) : 32;
  tight_preimages = argc > 27 ? stoi(argv[27]) != 0 : true;
  probe_percent = argc > 28 ? stoi(argv[28]) : 20;
  block_scheduler = argc > 29 ? stoi(argv[29]) : 0;
  subgrid_depth = argc > 30 ? stoi(argv[30]) : 0;
  if (memory < 2 || memory > 8 || bins < 1 || base <= 0 || base >= 1 ||
      maxstep < 1 || maxstep > 6 || outer_depth < 1 || outer_depth > 7 ||
      entry_depth < outer_depth || entry_depth > 7 || atlas_grid < 1 ||
      atlas_grid > 10000000 || max_cells < 1 || node_limit < 1 ||
      root_trials < 1 || root_step_budget < 1 || seconds_limit <= 0 ||
      block_span < 1 || block_span > 4096 || box_penalty < 0 ||
      probe_percent < 0 || probe_percent > 80 || block_scheduler < 0 ||
      block_scheduler > 2 || subgrid_depth < 0 || subgrid_depth > 6 ||
      (minimum_shape_memory &&
       (minimum_shape_memory < 2 || minimum_shape_memory > memory)))
    return 2;
  for (int n : {membership_samples, entry_samples})
    if (n != 1 && n != 3 && n != 11)
      return 2;
  for (const auto &w : {root_left, root_right})
    if (w.size() <= size_t(memory) || w.size() > 64 ||
        w.find_first_not_of("123") != string::npos || state(w) < 0)
      return 2;
  auto weight = [](string w) {
    auto m = mat(w);
    return m[2] * anchor + m[3];
  };
  if (weight(root_left) > weight(root_right))
    swap(root_left, root_right);
  double ratio = pow(weight(root_left) / weight(root_right), 2);
  prepare_catalog();
  int ls = shape_lookup.at(root_left.substr(root_left.size() - memory));
  int rs = shape_lookup.at(root_right.substr(root_right.size() - memory)),
      qi = -1;
  for (int i = 0; i < bins; ++i)
    if (qb[i].lo <= ratio && ratio <= qb[i].hi)
      qi = i;
  if (qi < 0)
    return 2;
  int root = lazy_cell(ls, rs,
                       (root_left.size() + root_right.size()) % 2 ? -1 : 1, qi);
  auto lm = mat(root_left), rm = mat(root_right);
  if (!(cells[root].r.lo <= lm[2] / lm[3] &&
        lm[2] / lm[3] <= cells[root].r.hi &&
        cells[root].sb.lo <= rm[2] / rm[3] &&
        rm[2] / rm[3] <= cells[root].sb.hi))
    return 2;
  BlockGame game({root, 0, 1}, block_scheduler == 0);
  game.prefer_shared = block_scheduler == 2;
  block_save(output, game, false);
  double discovery_limit = seconds_limit * (100 - probe_percent) / 100.;
  BlockGame::Planner planner =
      [&](const Block &key, const auto &dead) -> optional<BlockGame::Proposal> {
    check_time();
    if (elapsed() >= discovery_limit)
      throw SearchLimit("reserved time for finite closure probe");
    if (elapsed() - last_checkpoint > 15) {
      cerr << "block steps " << game.steps << " types " << game.entries.size()
           << " cells " << cells.size() << '\n';
      block_save(output, game, false);
    }
    return block_proposal(key, game, dead);
  };
  try {
    for (int trial = 0; trial < root_trials; ++trial) {
      int k = trial % 2 ? -(trial + 1) / 2 : trial / 2;
      if (trial)
        game.start_root({root, k, k + 1});
      ++tried_roots;
      game.run(planner, node_limit, game.steps + root_step_budget);
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
  if (!game.closed && probe_percent && elapsed() < seconds_limit) {
    // The probe has its OWN rejection set. A type excluded by this finite
    // dictionary must never be marked impossible in the discovery game.
    BlockGame probe(game.entries[game.root_id].key, true);
    probe.prefer_shared = block_scheduler == 2;
    probing = true;
    auto restricted = [&](const Block &key,
                          const auto &dead) -> optional<BlockGame::Proposal> {
      auto forbidden = [&](const Block &child) {
        return !game.ids.count(child) || dead(child);
      };
      return block_proposal(key, game, forbidden);
    };
    try {
      for (int trial = 0; trial < tried_roots; ++trial) {
        int k = trial % 2 ? -(trial + 1) / 2 : trial / 2;
        probe.start_root({root, k, k + 1});
        probe.run(restricted, game.entries.size(),
                  probe.steps + root_step_budget * 4);
        if (probe.closed)
          break;
      }
    } catch (const SearchLimit &error) {
      stop_reason += "; finite closure probe: " + string(error.what());
    }
    probe_steps = probe.steps;
    probe_rejections = probe.rejected;
    probe_closed = probe.closed;
    if (probe.closed) {
      game = move(probe);
      stop_reason =
          "finite closure probe found candidate requiring exact replay";
    }
    probing = false;
  }
  if (!game.closed)
    for (int i : game.supported_nodes())
      if (get<0>(game.entries[i].key) == root) {
        game.start_root(game.entries[i].key);
        game.closed = game.closure();
        if (game.closed)
          break;
      }
  block_save(output, game, true);
  cerr << "finished: " << stop_reason << "; blocks " << game.entries.size()
       << " closed=" << game.closed << '\n';
}
#endif
