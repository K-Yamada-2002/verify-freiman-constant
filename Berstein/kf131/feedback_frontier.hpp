// The Python adapter checks metadata and emits a simple discovery-only file.
// Loaded rules carry every child; they do not bypass the exact verifier.
#pragma once
long imported_types = 0, imported_rules = 0, imported_alternatives = 0;
void import_feedback_frontier(FeedbackRegistry<BlockGame> &registry,
                              const string &path, int limit) {
  ifstream input(path);
  string magic;
  int count = 0, root_index = -1;
  input >> magic >> count >> root_index;
  if ((magic != "kf131-frontier-v1" && magic != "kf131-frontier-v2" &&
       magic != "kf131-frontier-v3") ||
      count < 1 || count > limit || root_index < 0 || root_index >= count)
    throw runtime_error("invalid frontier header");
  struct ImportedCase {
    bool swap;
    int a, b;
    vector<int> children;
  };
  struct ImportedEdge {
    string u, v;
    vector<ImportedCase> cases;
  };
  auto read_edges = [&](int edges) {
    vector<ImportedEdge> result;
    for (int e = 0; e < edges; ++e) {
      ImportedEdge edge;
      int cases;
      input >> quoted(edge.u) >> quoted(edge.v) >> cases;
      if (!input || cases < 1 || cases > 2)
        throw runtime_error("invalid frontier edge");
      for (int k = 0; k < cases; ++k) {
        int sw, n;
        ImportedCase branch;
        input >> sw >> branch.a >> branch.b >> n;
        if (!input || sw < 0 || sw > 1 || branch.a >= branch.b || n < 1)
          throw runtime_error("invalid frontier branch");
        branch.swap = sw;
        for (int j = 0; j < n; ++j) {
          int target;
          input >> target;
          if (!input || target < 0 || target >= count)
            throw runtime_error("invalid frontier destination");
          branch.children.push_back(target);
        }
        edge.cases.push_back(move(branch));
      }
      result.push_back(move(edge));
    }
    return result;
  };
  vector<Block> keys;
  vector<vector<ImportedEdge>> plans(count);
  vector<bool> covered;
  for (int i = 0; i < count; ++i) {
    string left, right;
    int p, q, a, b, local, edges;
    int level = 0, part = 0;
    input >> quoted(left) >> quoted(right) >> p >> q;
    if (magic != "kf131-frontier-v1")
      input >> level >> part;
    input >> a >> b >> local >> edges;
    if (!input || !shape_lookup.count(left) || !shape_lookup.count(right) ||
        abs(p) != 1 || q < 0 || q >= bins || a >= b || edges < 0 ||
        (local != 0 && local != 1) || (!local && edges) || level < 0 ||
        level > ratio_max_depth || part < 0 || part >= (1 << level))
      throw runtime_error("invalid frontier node");
    keys.push_back({lazy_cell(shape_lookup.at(left), shape_lookup.at(right), p,
                              ratio_id(q, level, part)),
                    a, b});
    covered.push_back(local);
    plans[i] = read_edges(edges);
  }
  vector<pair<int, vector<ImportedEdge>>> alternatives;
  if (magic == "kf131-frontier-v3") {
    int total;
    if (!(input >> total) || total < 0)
      throw runtime_error("invalid alternative count");
    for (int i = 0; i < total; ++i) {
      int parent, edges;
      if (!(input >> parent >> edges) || parent < 0 || parent >= count ||
          edges < 1)
        throw runtime_error("invalid alternative rule");
      alternatives.push_back({parent, read_edges(edges)});
    }
  }
  const auto &loaded_root = cells[get<0>(keys[root_index])];
  const auto &original_root = cells[get<0>(registry.game.entries[0].key)];
  auto is_suffix = [](const string &word, const string &suffix) {
    return word.size() >= suffix.size() &&
           word.compare(word.size() - suffix.size(), suffix.size(), suffix) ==
               0;
  };
  auto lm = mat(root_left), rm = mat(root_right);
  if (!is_suffix(root_left, shapes[loaded_root.s].word) ||
      !is_suffix(root_right, shapes[loaded_root.t].word) ||
      loaded_root.p != original_root.p ||
      ratio_key(loaded_root.qi).bin != original_root.qi ||
      !(loaded_root.r.lo <= lm[2] / lm[3] &&
        lm[2] / lm[3] <= loaded_root.r.hi &&
        loaded_root.sb.lo <= rm[2] / rm[3] &&
        rm[2] / rm[3] <= loaded_root.sb.hi))
    throw runtime_error("frontier root parameter cell differs");
  for (const auto &key : keys)
    registry.ensure(key);
  if (registry.game.entries.size() > size_t(limit))
    throw runtime_error("frontier type limit");
  auto install = [&](int i, const vector<ImportedEdge> &plan) {
    int cid = get<0>(keys[i]);
    atlas_moves(cid);
    BlockGame::Proposal proposal;
    for (const auto &old : plan) {
      const auto &moves = cells[cid].moves;
      int mi = 0;
      while (mi < int(moves.size()) &&
             (moves[mi].u != old.u || moves[mi].v != old.v))
        ++mi;
      if (mi == int(moves.size()))
        throw runtime_error("frontier move unavailable in this geometry");
      BlockEdge edge{mi, {}, {-1e90, 1e90}};
      for (const auto &branch : old.cases) {
        BlockCase next{branch.swap, branch.a, branch.b, {}};
        for (int child : branch.children) {
          next.targets.push_back(keys[child]);
          proposal.children.push_back(keys[child]);
        }
        edge.cases.push_back(move(next));
      }
      proposal.plan.edges.push_back(move(edge));
    }
    if (!registry.install(keys[i], proposal, limit))
      throw runtime_error("frontier rule exceeds type limit");
  };
  // Record every alternative first; restore the selected plans last.
  for (const auto &alternative : alternatives) {
    install(alternative.first, alternative.second);
    ++imported_alternatives;
  }
  for (int i = 0; i < count; ++i) {
    if (covered[i]) {
      install(i, plans[i]);
      ++imported_rules;
    } else
      registry.withdraw(keys[i]);
  }
  imported_types = count;
  registry.game.root_id = registry.game.ids.at(keys[root_index]);
}
