// Conditional finite-dictionary failures are soft ranking evidence only.
// They never enter the geometric impossibility set or remove a legal edge.
#pragma once
struct FeedbackLearning {
  map<Block, long> failures;
  map<Block, vector<Block>> last_repair;
  vector<double> risk;
  double weight = 0;
  long observations = 0, repeated = 0, same_repairs = 0, changed_repairs = 0;
  long imported = 0;

  void failed(const Block &key) {
    auto &count = failures[key];
    repeated += count != 0;
    ++count;
    ++observations;
  }
  void repair(const Block &key, const vector<Block> &children) {
    auto old = last_repair.find(key);
    if (old != last_repair.end()) {
      same_repairs += old->second == children;
      changed_repairs += old->second != children;
    }
    last_repair[key] = children;
  }
  void refresh(const BlockGame &game) {
    risk.assign(game.entries.size(), 0);
    for (size_t i = 0; i < risk.size(); ++i)
      risk[i] = game.entries[i].status == BlockGame::Local ? 0 : 1;
    // AND dependencies: a single open descendant matters. Three discounted
    // propagation steps expose locally covered but still unsupported types.
    for (int step = 0; step < 3; ++step) {
      auto next = risk;
      for (size_t i = 0; i < risk.size(); ++i)
        for (int child : game.entries[i].children)
          next[i] = max(next[i], .75 * risk[child]);
      risk.swap(next);
    }
  }
  double cost(Block key, const BlockGame &game) const {
    auto [cid, lo, hi] = key;
    // A virtual descriptor may have been materialized since it was cached.
    if (cid < 0)
      key = {peek_cell(cid), lo, hi};
    auto found = game.ids.find(key);
    double cost = found == game.ids.end()                                  ? 8
                  : game.entries[found->second].status == BlockGame::Local ? 0
                                                                           : 1;
    if (found != game.ids.end() && size_t(found->second) < risk.size())
      cost += weight * risk[found->second];
    auto failed = failures.find(key);
    if (failed != failures.end())
      cost += weight * log2(1. + failed->second);
    return cost;
  }
  void save(const string &path) const {
    ofstream out(path + ".tmp");
    out << setprecision(17) << "kf131-learning-v1 " << base << ' ' << bins
        << ' ' << atlas_grid << '\n';
    for (auto [key, count] : failures) {
      auto [cid, lo, hi] = key;
      const auto &c = cells.at(cid);
      auto q = ratio_key(c.qi);
      out << shapes[c.s].word << ' ' << shapes[c.t].word << ' ' << c.p << ' '
          << q.bin << ' ' << q.level << ' ' << q.index << ' ' << lo << ' ' << hi
          << ' ' << count << '\n';
    }
    out.close();
    if (!out)
      throw runtime_error("cannot save learning history");
    if (rename((path + ".tmp").c_str(), path.c_str()))
      throw runtime_error("cannot replace learning history");
  }
  void load(const string &path) {
    ifstream in(path);
    string magic, left, right;
    double b;
    int nb, grid;
    if (!(in >> magic >> b >> nb >> grid) || magic != "kf131-learning-v1" ||
        b != base || nb != bins || grid != atlas_grid)
      throw runtime_error("learning history geometry mismatch");
    while (in >> left) {
      int p, bin, level, part, lo, hi;
      long count;
      if (!(in >> right >> p >> bin >> level >> part >> lo >> hi >> count) ||
          !shape_lookup.count(left) || !shape_lookup.count(right) ||
          (p != 1 && p != -1) || bin < 0 || bin >= bins || level < 0 ||
          level > ratio_max_depth || part < 0 || part >= (1 << level) ||
          lo >= hi || count < 1)
        throw runtime_error("invalid learning history row");
      int q = ratio_id(bin, level, part);
      int cid = lazy_cell(shape_lookup.at(left), shape_lookup.at(right), p, q);
      failures[{cid, lo, hi}] = count;
      ++imported;
    }
    if (!in.eof())
      throw runtime_error("invalid learning history tail");
  }
};
