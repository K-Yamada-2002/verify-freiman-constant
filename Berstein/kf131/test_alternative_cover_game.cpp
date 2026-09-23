#include "finite_cover_game.hpp"
#include "feedback_registry.hpp"
#include "alternative_cover_game.hpp"
#include <cassert>
#include <iostream>
#include <random>
using Game = FiniteCoverGame<int, int>;
int main() {
  // Neither current selected graph nor the earlier selection closes.
  // The retained a->b and later b->a rules jointly close a genuine cycle.
  FeedbackRegistry<Game> registry(Game::Entry{0});
  auto &game = registry.game;
  AlternativeCoverGame<Game> bank;
  registry.install(0, {10, {1}}, 100);
  bank.record(game, 0);
  registry.install(0, {11, {2}}, 100);
  bank.record(game, 0);
  registry.install(1, {12, {0}}, 100);
  bank.record(game, game.ids.at(1));
  auto old = bank.propose(
      game, 0, [&](int i) { return i == game.ids.at(2); },
      [](int) { return 0.; });
  assert(old && old->plan == 10 && old->children == std::vector<int>{1});
  assert(!bank.propose(
      game, 0, [](int) { return true; }, [](int) { return 0.; }));
  assert(game.supported_nodes().empty());
  auto core = bank.supported(game.entries.size());
  assert(core.nodes.size() == 2);
  bank.materialize(game, core);
  assert(game.closure() && game.entries[0].plan == 10);
  // Every child is mandatory; an unavailable second child kills the rule.
  std::vector<bool> blocked(game.entries.size());
  blocked[game.ids.at(1)] = true;
  assert(bank.supported(game.entries.size(), blocked).nodes.empty());
  std::mt19937 rng(131);
  for (int trial = 0; trial < 1000; ++trial) {
    int n = 1 + rng() % 7;
    FeedbackRegistry<Game> r(Game::Entry{0});
    for (int i = 0; i < n; ++i)
      r.ensure(i);
    AlternativeCoverGame<Game> b;
    for (int i = 0; i < 20; ++i) {
      std::vector<int> children;
      int m = 1 + rng() % 3;
      for (int j = 0; j < m; ++j)
        children.push_back(rng() % n);
      int parent = rng() % n;
      r.install(parent, {i, children}, n);
      b.record(r.game, parent);
    }
    std::vector<bool> forbidden(n);
    for (int i = 0; i < n; ++i)
      forbidden[i] = rng() % 5 == 0;
    unsigned union_valid = 0;
    for (unsigned mask = 0; mask < (1u << n); ++mask) {
      bool valid = true;
      for (int i = 0; i < n && valid; ++i)
        if (mask & (1u << i)) {
          bool rule_found = false;
          if (!forbidden[i])
            for (const auto &rule : b.rules)
              if (rule.parent == i) {
                bool all = true;
                for (int child : rule.children)
                  all = all && (mask & (1u << child));
                rule_found = rule_found || all;
              }
          valid = rule_found;
        }
      if (valid)
        union_valid |= mask;
    }
    auto answer = b.supported(n, forbidden);
    unsigned actual = 0;
    for (int i : answer.nodes)
      actual |= 1u << i;
    assert(actual == union_valid);
  }
  std::cout
      << "alternative cycle recovery and 1000 exhaustive subset games passed\n";
}
