#include "finite_cover_game.hpp"
#include "feedback_registry.hpp"
#include "alternative_cover_game.hpp"
#include "global_frontier.hpp"
#include <cassert>
#include <iostream>
#include <random>
using Game = FiniteCoverGame<int, int>;
int main() {
  FeedbackRegistry<Game> registry(Game::Entry{0});
  auto &game = registry.game;
  for (int i = 1; i < 6; ++i)
    registry.ensure(i);
  AlternativeCoverGame<Game> bank;
  registry.on_install = [&](const Game &g, int i) { bank.record(g, i); };
  registry.install(0, {0, {1}}, 100);
  registry.install(2, {1, {3, 4}}, 100);
  registry.install(3, {2, {2}}, 100);
  std::vector<bool> blocked(6);
  GlobalFrontier<Game> scheduling;
  auto tasks = scheduling.rank(game, bank, blocked, true);
  assert(tasks[0].node == 4 && tasks[0].cyclic_references == 1);
  assert(scheduling.cyclic_nodes == 2 && scheduling.eligible == 3);
  auto diverse = scheduling.rank(game, bank, blocked, true, true, true);
  assert(scheduling.return_distance[2] == 0 &&
         scheduling.return_distance[4] < 0);
  assert(std::any_of(diverse.begin(), diverse.end(),
                     [](auto t) { return t.node == 2 && t.diversify; }));
  auto reached = game.reachable();
  assert(std::find(reached.begin(), reached.end(), 4) == reached.end());
  registry.install(4, {3, {2}}, 100);
  auto core = bank.supported(game.entries.size());
  assert(core.nodes == std::vector<int>({2, 3, 4}));
  assert(!game.closure());
  blocked[4] = true;
  tasks = scheduling.rank(game, bank, blocked, true);
  assert(std::find_if(tasks.begin(), tasks.end(),
                      [](auto t) { return t.node == 2; }) != tasks.end());
  assert(std::find_if(tasks.begin(), tasks.end(),
                      [](auto t) { return t.node == 4; }) == tasks.end());
  auto focus = scheduling.rank(game, bank, blocked, true, true);
  assert(focus[0].node == 2 && focus[0].cycle_distance == 0);
  scheduling.note(1, false, false, bank.rules.size() + 1);
  tasks = scheduling.rank(game, bank, blocked, false);
  assert(std::find_if(tasks.begin(), tasks.end(),
                      [](auto t) { return t.node == 1; }) == tasks.end());
  registry.install(5, {4, {1}}, 100);
  tasks = scheduling.rank(game, bank, blocked, false);
  assert(std::find_if(tasks.begin(), tasks.end(),
                      [](auto t) { return t.node == 1; }) != tasks.end());
  std::mt19937 rng(131);
  for (int trial = 0; trial < 1000; ++trial) {
    int n = 1 + rng() % 8;
    FeedbackRegistry<Game> r(Game::Entry{0});
    for (int i = 0; i < n; ++i)
      r.ensure(i);
    AlternativeCoverGame<Game> b;
    for (int i = 0; i < 15; ++i) {
      std::vector<int> children;
      for (int j = 0; j < int(1 + rng() % 3); ++j)
        children.push_back(rng() % n);
      int parent = rng() % n;
      r.install(parent, {i, children}, n);
      b.record(r.game, parent);
    }
    std::vector<bool> excluded(n);
    for (int i = 0; i < n; ++i)
      excluded[i] = rng() % 5 == 0;
    std::vector<std::vector<bool>> paths(n, std::vector<bool>(n));
    std::vector<int> valid(n);
    for (const auto &rule : b.rules) {
      bool ok = !excluded[rule.parent];
      for (int child : rule.children)
        ok = ok && !excluded[child];
      if (ok) {
        ++valid[rule.parent];
        for (int child : rule.children)
          paths[rule.parent][child] = true;
      }
    }
    for (int k = 0; k < n; ++k)
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
          paths[i][j] = paths[i][j] || (paths[i][k] && paths[k][j]);
    int cycles = 0;
    for (int i = 0; i < n; ++i)
      cycles += paths[i][i];
    GlobalFrontier<Game> g;
    auto ranked = g.rank(r.game, b, excluded, true);
    assert(g.cyclic_nodes == cycles);
    for (auto task : ranked)
      assert(!excluded[task.node] && !valid[task.node]);
    int expected = 0;
    for (int i = 0; i < n; ++i)
      expected += !valid[i] && !excluded[i];
    assert(ranked.size() == size_t(expected));
    // The focused policy may retain useful dependency arcs from a rule
    // whose other mandatory child is blocked. These arcs affect priority
    // only. Check its raw SCC and backward reachability independently.
    std::vector<std::vector<bool>> raw(n, std::vector<bool>(n));
    for (const auto &rule : b.rules)
      if (!excluded[rule.parent])
        for (int child : rule.children)
          if (!excluded[child])
            raw[rule.parent][child] = true;
    for (int k = 0; k < n; ++k)
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
          raw[i][j] = raw[i][j] || (raw[i][k] && raw[k][j]);
    auto focused = g.rank(r.game, b, excluded, true, true, true);
    int raw_cycles = 0;
    for (int i = 0; i < n; ++i) {
      raw_cycles += raw[i][i];
      bool returns = false;
      for (int j = 0; j < n; ++j)
        returns = returns || (raw[i][j] && raw[j][j]);
      assert((g.return_distance[i] >= 0) == returns);
    }
    assert(g.cyclic_nodes == raw_cycles);
    for (auto t : focused)
      assert(!excluded[t.node] &&
             (!valid[t.node] || g.return_distance[t.node] >= 0));
  }
  std::cout << "off-root cycle completion, mandatory children, retry revision, "
               "1000 SCC comparisons passed\n";
}
