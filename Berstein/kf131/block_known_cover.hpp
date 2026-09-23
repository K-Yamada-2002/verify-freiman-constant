// Recombine already discovered interval obligations. Several successor maps
// may cover even a single grid atom, with contacts between grid points.
#pragma once
long known_cover_queries = 0, known_cover_successes = 0;
bool trim_known_ranges = false;
long known_range_trims = 0, known_range_atoms_removed = 0;
using BlockDomain = vector<pair<int, int>>;
BlockDomain block_intersection(const BlockDomain &a, const BlockDomain &b) {
  BlockDomain out;
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    int lo = max(a[i].first, b[j].first), hi = min(a[i].second, b[j].second);
    if (lo < hi)
      out.push_back({lo, hi});
    if (a[i].second < b[j].second)
      ++i;
    else
      ++j;
  }
  return out;
}
struct KnownSlice {
  vector<Block> keys;
  BlockDomain domain;
};
struct KnownBlocks : KnownSlice {
  vector<KnownSlice> slices;
};
void merge_known_slice(KnownSlice &out) {
  sort(out.keys.begin(), out.keys.end(), [](const auto &a, const auto &b) {
    return pair<int, int>{get<1>(a), get<2>(a)} <
           pair<int, int>{get<1>(b), get<2>(b)};
  });
  for (auto [cid, lo, hi] : out.keys) {
    if (!out.domain.empty() && lo <= out.domain.back().second)
      out.domain.back().second = max(out.domain.back().second, hi);
    else
      out.domain.push_back({lo, hi});
  }
}
KnownBlocks known_blocks(int descriptor, const BlockGame &game,
                         const function<bool(const Block &)> &dead,
                         Bounds required = {0, 1}) {
  CellKey original = descriptor >= 0
                         ? CellKey{cells[descriptor].s, cells[descriptor].t,
                                   cells[descriptor].p, cells[descriptor].qi}
                         : virtual_boxes[-1 - descriptor];
  auto [si, ti, p, q] = original;
  string left = shapes[si].word, right = shapes[ti].word;
  int last = max(left.size(), right.size());
  int first = minimum_shape_memory ? minimum_shape_memory : last;
  KnownBlocks out;
  required = {max(required.lo, qb[q].lo), min(required.hi, qb[q].hi)};
  vector<int> ratio_choices{q};
  if (ratio_max_depth) {
    int bin = ratio_key(q).bin;
    for (auto it = ratio_ids.lower_bound({bin, 0, 0});
         it != ratio_ids.end() && get<0>(it->first) == bin; ++it) {
      int id = it->second;
      if (id != q && qb[id].lo < required.hi && required.lo < qb[id].hi)
        ratio_choices.push_back(id);
    }
  }
  for (int level = first; level <= last; ++level) {
    int ls = shape_lookup.at(
        left.substr(left.size() - min(int(left.size()), level)));
    int rs = shape_lookup.at(
        right.substr(right.size() - min(int(right.size()), level)));
    for (int ratio : ratio_choices) {
      auto existing = lazy_ids.find({ls, rs, p, ratio});
      if (existing == lazy_ids.end())
        continue;
      auto found = existing_blocks.find(existing->second);
      if (found == existing_blocks.end())
        continue;
      for (auto [_, id] : found->second) {
        const auto &e = game.entries[id];
        if ((probing || e.status == BlockGame::Local) && !dead(e.key))
          out.keys.push_back(e.key);
      }
    }
  }
  if (ratio_choices.size() == 1) {
    merge_known_slice(out);
    return out;
  }
  // Scalar coverage must hold on EVERY required ratio strip. Taking only
  // the projections of the union would incorrectly fill diagonal holes.
  set<double> cuts{required.lo, required.hi};
  for (auto [cid, a, b] : out.keys)
    for (double h : {cells[cid].q.lo, cells[cid].q.hi})
      if (required.lo < h && h < required.hi)
        cuts.insert(h);
  for (auto it = cuts.begin(); next(it) != cuts.end(); ++it) {
    double a = *it, b = *next(it);
    KnownSlice slice;
    for (auto key : out.keys) {
      Bounds box = cells[get<0>(key)].q;
      if (box.lo <= a + 1e-14 && b <= box.hi + 1e-14)
        slice.keys.push_back(key);
    }
    merge_known_slice(slice);
    out.domain = out.slices.empty()
                     ? slice.domain
                     : block_intersection(out.domain, slice.domain);
    out.slices.push_back(move(slice));
    if (out.domain.empty())
      break;
  }
  return out;
}
vector<Block> known_slice_chain(const KnownSlice &bank, int lo, int hi) {
  vector<Block> selected;
  if (learned_block_cost) {
    ++weighted_slice_queries;
    vector<WeightedInterval> offers;
    for (auto key : bank.keys)
      offers.push_back({double(get<1>(key)), double(get<2>(key)),
                        1 + learned_block_cost(key)});
    auto chain = minimum_interval_chain(offers, lo, hi);
    if (!chain)
      throw logic_error("weighted interval union lost a component");
    for (int i : *chain)
      selected.push_back(bank.keys[i]);
    return selected;
  }
  int current = lo;
  size_t pos = 0;
  while (current < hi) {
    int farthest = current;
    optional<Block> best;
    while (pos < bank.keys.size() && get<1>(bank.keys[pos]) <= current) {
      if (get<2>(bank.keys[pos]) > farthest) {
        farthest = get<2>(bank.keys[pos]);
        best = bank.keys[pos];
      }
      ++pos;
    }
    if (!best)
      throw logic_error("known interval union lost a component");
    selected.push_back(*best);
    current = farthest;
  }
  return selected;
}
vector<Block> known_chain(const KnownBlocks &bank, int lo, int hi) {
  if (bank.slices.empty())
    return known_slice_chain(bank, lo, hi);
  vector<Block> out;
  for (const auto &slice : bank.slices) {
    auto chain = known_slice_chain(slice, lo, hi);
    out.insert(out.end(), chain.begin(), chain.end());
  }
  sort(out.begin(), out.end());
  out.erase(unique(out.begin(), out.end()), out.end());
  return out;
}
optional<vector<BlockEdge>>
progressing_edges(const vector<BlockEdge> &candidates, double lo, double hi) {
  vector<BlockEdge> chosen;
  if (learned_block_cost) {
    ++weighted_edge_queries;
    vector<WeightedInterval> offers;
    for (const auto &edge : candidates) {
      set<Block> children;
      for (const auto &branch : edge.cases)
        children.insert(branch.targets.begin(), branch.targets.end());
      double cost = 1;
      for (auto child : children)
        cost += 1 + learned_block_cost(child);
      offers.push_back({edge.core.lo, edge.core.hi, cost});
    }
    auto chain = minimum_interval_chain(offers, lo, hi, 1e-13, 1e-14);
    if (!chain || chain->empty())
      return nullopt;
    for (int i : *chain)
      chosen.push_back(candidates[i]);
    return chosen;
  }
  double current = lo;
  while (current < hi - 1e-13) {
    int best = -1;
    for (int i = 0; i < int(candidates.size()); ++i)
      if (candidates[i].core.lo <= current + 1e-13 &&
          candidates[i].core.hi > current + 1e-14 &&
          (best < 0 || candidates[i].core.hi > candidates[best].core.hi))
        best = i;
    if (best < 0)
      return nullopt;
    current = candidates[best].core.hi;
    chosen.push_back(candidates[best]);
  }
  if (chosen.empty())
    return nullopt;
  return chosen;
}
optional<vector<BlockEdge>>
known_cover(int cid, int lo, int hi, BlockGame &game,
            const function<bool(const Block &)> &dead) {
  ++known_cover_queries;
  atlas_moves(cid);
  const auto &c = cells[cid];
  using BankKey = tuple<int, double, double>;
  map<BankKey, KnownBlocks> banks;
  vector<BlockEdge> offers;
  for (int mi = 0; mi < int(c.moves.size()); ++mi) {
    check_time();
    const auto &m = c.moves[mi];
    vector<BlockEdge> sides[2];
    bool required[2] = {false, false}, valid = true;
    for (bool sw : {false, true}) {
      vector<BankKey> deps;
      BlockDomain common;
      for (auto d : m.deps)
        if (d.swap == sw) {
          BankKey key{d.cell, d.required_ratio.lo, d.required_ratio.hi};
          if (!banks.count(key))
            banks.emplace(key,
                          known_blocks(d.cell, game, dead, d.required_ratio));
          const auto &bank = banks.at(key);
          common = deps.empty() ? bank.domain
                                : block_intersection(common, bank.domain);
          deps.push_back(key);
          if (common.empty()) {
            valid = false;
            break;
          }
        }
      if (!valid)
        break;
      required[sw] = !deps.empty();
      for (auto [a, b] : common) {
        auto core = discovery_core(c, m, sw, a, b);
        if (core.lo >= core.hi || core.hi <= double(lo) / atlas_grid ||
            core.lo >= double(hi) / atlas_grid)
          continue;
        if (trim_known_ranges) {
          auto trimmed = discovery_trim(c, m, sw, {a, b},
                                        max(core.lo, double(lo) / atlas_grid),
                                        min(core.hi, double(hi) / atlas_grid));
          if (trimmed != make_pair(a, b)) {
            ++known_range_trims;
            known_range_atoms_removed +=
                b - a - (trimmed.second - trimmed.first);
            tie(a, b) = trimmed;
            core = discovery_core(c, m, sw, a, b);
          }
        }
        BlockCase branch{sw, a, b, {}};
        for (const auto &raw : deps) {
          auto chain = known_chain(banks.at(raw), a, b);
          branch.targets.insert(branch.targets.end(), chain.begin(),
                                chain.end());
        }
        sides[sw].push_back({mi, {move(branch)}, core});
      }
    }
    if (!valid)
      continue;
    if (required[0] && required[1]) {
      for (const auto &a : sides[0])
        for (const auto &b : sides[1]) {
          Bounds core{max(a.core.lo, b.core.lo), min(a.core.hi, b.core.hi)};
          if (core.lo < core.hi)
            offers.push_back({mi, {a.cases[0], b.cases[0]}, core});
        }
    } else {
      auto &side = sides[required[1]];
      offers.insert(offers.end(), side.begin(), side.end());
    }
  }
  auto result = progressing_edges(offers, double(lo) / atlas_grid,
                                  double(hi) / atlas_grid);
  if (result)
    ++known_cover_successes;
  return result;
}
