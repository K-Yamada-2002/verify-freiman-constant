// Greatest fixed point in a finite AND/OR hypergraph of complete local rules.
// Alternatives are retained even when the currently chosen rule is replaced.
#pragma once
#include <algorithm>
#include <deque>
#include <map>
#include <limits>
#include <optional>
#include <set>
#include <vector>
template <class Game> class AlternativeCoverGame {
public:
  using Plan = decltype(typename Game::Entry{}.plan);
  struct Rule {
    int parent;
    Plan plan;
    std::vector<int> children;
  };
  struct Core {
    std::vector<int> nodes, rule;
  };
  std::vector<Rule> rules;
  std::vector<std::vector<int>> by_parent, by_child;
  std::set<std::pair<int, std::vector<int>>> seen;
  void record(const Game &game, int parent) {
    by_parent.resize(game.entries.size());
    by_child.resize(game.entries.size());
    const auto &entry = game.entries.at(parent);
    if (entry.status != Game::Local)
      return;
    auto children = entry.children;
    std::sort(children.begin(), children.end());
    children.erase(std::unique(children.begin(), children.end()),
                   children.end());
    if (!seen.insert({parent, children}).second)
      return;
    int id = rules.size();
    rules.push_back({parent, entry.plan, children});
    by_parent[parent].push_back(id);
    for (int child : children)
      by_child[child].push_back(id);
  }
  // Reuse a complete stored rule before asking the geometry planner again.
  // All mandatory children must survive the current frozen-dictionary probe.
  template <class Dead, class Cost>
  std::optional<typename Game::Proposal> propose(const Game &game, int parent,
                                                 Dead dead, Cost cost) const {
    if (parent < 0 || parent >= int(by_parent.size()))
      return std::nullopt;
    int best = -1;
    double best_cost = std::numeric_limits<double>::infinity();
    for (int id : by_parent[parent]) {
      double total = 0;
      bool valid = true;
      for (int child : rules[id].children) {
        if (dead(child)) {
          valid = false;
          break;
        }
        total += 1 + cost(child);
      }
      if (valid && total < best_cost) {
        best = id;
        best_cost = total;
      }
    }
    if (best < 0)
      return std::nullopt;
    typename Game::Proposal answer{rules[best].plan, {}};
    for (int child : rules[best].children)
      answer.children.push_back(game.entries[child].key);
    return answer;
  }
  Core supported(size_t size, const std::vector<bool> &blocked = {}) const {
    std::vector<int> count(size);
    std::vector<bool> alive(size, true), viable(rules.size(), true);
    std::deque<int> failed;
    for (int i = 0; i < int(size); ++i) {
      count[i] = i < int(by_parent.size()) ? by_parent[i].size() : 0;
      if (!count[i] || (i < int(blocked.size()) && blocked[i])) {
        alive[i] = false;
        failed.push_back(i);
      }
    }
    while (!failed.empty()) {
      int child = failed.front();
      failed.pop_front();
      if (child >= int(by_child.size()))
        continue;
      for (int edge : by_child[child])
        if (viable[edge]) {
          viable[edge] = false;
          int parent = rules[edge].parent;
          if (--count[parent] == 0 && alive[parent]) {
            alive[parent] = false;
            failed.push_back(parent);
          }
        }
    }
    Core core;
    core.rule.assign(size, -1);
    for (int i = 0; i < int(size); ++i)
      if (alive[i]) {
        core.nodes.push_back(i);
        for (int edge : by_parent[i])
          if (viable[edge]) {
            core.rule[i] = edge;
            break;
          }
      }
    return core;
  }
  void materialize(Game &game, const Core &core) const {
    for (int id : core.nodes) {
      auto &entry = game.entries[id];
      for (int child : entry.children)
        game.entries[child].parents.erase(id);
      const auto &rule = rules.at(core.rule[id]);
      entry.plan = rule.plan;
      entry.children = rule.children;
      entry.status = Game::Local;
      for (int child : entry.children)
        game.entries[child].parents.insert(id);
    }
  }
};
