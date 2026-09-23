// Search for an actual legal cylinder pair inside a supported parameter box.
// This is only a proposal; ScalarVerifier.seed recomputes everything exactly.
#pragma once
struct SeedPrefix {
  string word;
  double weight, shape;
};
map<int, array<vector<SeedPrefix>, 2>> seed_prefix_cache;
const array<vector<SeedPrefix>, 2> &seed_prefixes(int shape) {
  auto found = seed_prefix_cache.find(shape);
  if (found != seed_prefix_cache.end())
    return found->second;
  array<vector<SeedPrefix>, 2> choices;
  for (int length = 0; length <= 6; ++length)
    for (const auto &middle : words(0, length)) {
      string word = "2" + middle + shapes[shape].word;
      if (state(word) < 0)
        continue;
      auto m = mat(word);
      double r = m[2] / m[3];
      if (r < shapes[shape].r.lo || r > shapes[shape].r.hi)
        continue;
      choices[word.size() % 2].push_back({word, m[2] * anchor + m[3], r});
    }
  for (auto &group : choices)
    sort(group.begin(), group.end(),
         [](const auto &a, const auto &b) { return a.weight < b.weight; });
  return seed_prefix_cache.emplace(shape, move(choices)).first->second;
}
optional<pair<string, string>> realize_cell(int cid) {
  const auto &c = cells[cid];
  const auto &left = seed_prefixes(c.s), &right = seed_prefixes(c.t);
  for (int parity = 0; parity < 2; ++parity) {
    const auto &other = right[parity ^ (c.p < 0)];
    for (const auto &a : left[parity]) {
      double low = a.weight / sqrt(c.q.hi), high = a.weight / sqrt(c.q.lo);
      auto b = lower_bound(
          other.begin(), other.end(), low * (1 + 1e-12),
          [](const auto &entry, double value) { return entry.weight < value; });
      if (b != other.end() && b->weight < high * (1 - 1e-12))
        return pair<string, string>{a.word, b->word};
    }
  }
  return nullopt;
}
long supported_seed_checks = 0, supported_node_count = 0;
bool salvage_supported_seed(BlockGame &game) {
  auto supported = game.supported_nodes();
  supported_node_count = supported.size();
  set<int> tried;
  for (int i : supported) {
    int cid = get<0>(game.entries[i].key);
    if (!tried.insert(cid).second)
      continue;
    check_time();
    ++supported_seed_checks;
    auto seed = realize_cell(cid);
    if (!seed)
      continue;
    root_left = seed->first;
    root_right = seed->second;
    game.root_id = i;
    game.closed = game.closure();
    if (game.closed)
      return true;
  }
  return false;
}
