#include "finite_cover_game.hpp"
#include <cassert>
#include <iostream>
#include <random>
using Game = FiniteCoverGame<int, int>;
using Proposal = Game::Proposal;

int main() {
  // A rejected child triggers an alternative. A genuinely closed cycle is
  // accepted; the irrelevant failed branch is absent from the final graph.
  Game alternative(0);
  alternative.run(
      [](int k, const auto &dead) -> std::optional<Proposal> {
        if (k == 0)
          return Proposal{0, {dead(1) ? 2 : 1}};
        if (k == 1)
          return std::nullopt;
        return Proposal{2, {2}};
      },
      10, 100);
  assert(alternative.closed && alternative.replans == 1);
  assert(alternative.reachable().size() == 2);

  // Every child of a chosen cover is mandatory, including siblings which
  // are discovered after an otherwise viable cyclic branch.
  Game conjunction(0);
  conjunction.run(
      [](int k, const auto &dead) -> std::optional<Proposal> {
        if (k == 0 && !dead(2))
          return Proposal{0, {1, 2}};
        if (k == 1)
          return Proposal{1, {1}};
        return std::nullopt;
      },
      10, 100);
  assert(!conjunction.closed &&
         conjunction.entries[0].status == Game::Rejected);
  // A failed root must not hide a different closed component that was
  // already discovered. No pending or rejected ancestor belongs to it.
  auto supported = conjunction.supported_nodes();
  assert(supported.size() == 1);
  assert(conjunction.entries[supported[0]].key == 1);
  conjunction.start_root(1);
  assert(conjunction.closure());

  // A finite frontier is never interpreted as an induction hypothesis.
  for (int budget : {1, 2, 3}) {
    Game frontier(0);
    frontier.run(
        [](int k, const auto &) -> std::optional<Proposal> {
          return Proposal{k, {k + 1}};
        },
        budget, 100);
    assert(!frontier.closed && frontier.limit_reached);
    assert(frontier.entries.size() <= static_cast<size_t>(budget));
  }

  // Once a parent switches plans, failure of an old sibling must not
  // invalidate its new plan or add a stale reverse dependency.
  Game stale(0);
  stale.run(
      [](int k, const auto &dead) -> std::optional<Proposal> {
        if (k == 0)
          return dead(1) ? Proposal{0, {3}} : Proposal{0, {1, 2}};
        if (k == 3)
          return Proposal{3, {3}};
        return std::nullopt;
      },
      10, 100);
  assert(stale.closed && stale.replans == 1 && stale.rejected == 2);
  assert(stale.entries[stale.ids.at(2)].parents.empty());

  Game steps(0);
  steps.run(
      [](int k, const auto &) -> std::optional<Proposal> {
        return Proposal{k, {k + 1}};
      },
      100, 2);
  assert(!steps.closed && steps.limit_reached && steps.steps == 2);

  Game reseed(0, true);
  auto plan_seed = [](int k, const auto &) -> std::optional<Proposal> {
    if (k == 0)
      return std::nullopt;
    return Proposal{1, {1}};
  };
  reseed.run(plan_seed, 10, 100);
  assert(!reseed.closed && reseed.entries[0].status == Game::Rejected);
  reseed.start_root(1);
  reseed.run(plan_seed, 10, 100);
  assert(reseed.closed && reseed.entries[0].status == Game::Rejected);
  assert(reseed.reachable().size() == 1);

  // A separate finite-domain probe can find a cycle which the discovery
  // policy overlooks while it follows an indefinitely growing alternative.
  Game discovering(0, true);
  auto growing_first = [](int k, const auto &dead) -> std::optional<Proposal> {
    if (!dead(k + 1))
      return Proposal{0, {k + 1}};
    return Proposal{1, {k}};
  };
  discovering.run(growing_first, 8, 100);
  assert(!discovering.closed);
  Game probe(0, true);
  probe.run(
      [&](int k, const auto &dead) {
        auto forbidden = [&](int child) {
          return !discovering.ids.count(child) || dead(child);
        };
        return growing_first(k, forbidden);
      },
      discovering.entries.size(), 100);
  assert(probe.closed && !discovering.closed);
  assert(discovering.rejected == 0);

  Game enlarged(0);
  enlarged.run(
      [](int, const auto &) -> std::optional<Proposal> { return std::nullopt; },
      10, 10);
  assert(enlarged.entries[0].status == Game::Rejected);
  enlarged.reconsider_rejections(0);
  enlarged.run(
      [](int k, const auto &) -> std::optional<Proposal> {
        return Proposal{k, {1}};
      },
      10, 100);
  assert(enlarged.closed && enlarged.entries.size() == 2);
  // Compare lazy discovery/backtracking with a separately computed greatest
  // fixed point on 100 finite games, including branching and long cycles.
  std::mt19937 random(131);
  int wins = 0, losses = 0;
  for (int example = 0; example < 100; ++example) {
    constexpr int n = 180;
    std::vector<std::vector<std::vector<int>>> rules(n);
    for (int i = 0; i < n; ++i) {
      int count =
          example % 2 ? random() % 4 : (random() % 12 ? 2 + random() % 3 : 0);
      for (int j = count; j > 0; --j)
        rules[i].push_back({int(random() % n), int(random() % n)});
    }
    std::vector<bool> alive(n, true);
    bool changed = true;
    while (changed) {
      changed = false;
      for (int i = 0; i < n; ++i)
        if (alive[i]) {
          bool supported = false;
          for (const auto &rule : rules[i]) {
            bool valid = true;
            for (int j : rule)
              valid = valid && alive[j];
            supported = supported || valid;
          }
          if (!supported) {
            alive[i] = false;
            changed = true;
          }
        }
    }
    for (int policy : {0, 1, 2}) {
      Game lazy(0, policy == 1);
      lazy.prefer_shared = policy == 2;
      lazy.run(
          [&](int k, const auto &dead) -> std::optional<Proposal> {
            for (const auto &rule : rules[k]) {
              bool valid = true;
              for (int j : rule)
                valid = valid && !dead(j);
              if (valid)
                return Proposal{k, rule};
            }
            return std::nullopt;
          },
          n, 100000);
      assert(!lazy.limit_reached && lazy.closed == alive[0]);
    }
    alive[0] ? ++wins : ++losses;
  }
  assert(wins > 10 && losses > 10);
  std::cout << "finite cover game: 9 scenarios and 300 fixed-point comparisons "
               "passed\n";
}
