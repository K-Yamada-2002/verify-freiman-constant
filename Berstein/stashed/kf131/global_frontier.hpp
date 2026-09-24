// Discovery scheduling across ALL retained alternatives, not just the current
// selected root. Scores never establish validity or remove mandatory children.
#pragma once
#include <algorithm>
#include <cmath>
#include <deque>
#include <numeric>
#include <utility>
#include <vector>

template <class Game> class GlobalFrontier {
public:
  struct Task {
    int node;
    double score;
    int references, one_missing, cyclic_references;
    int cycle_distance;
    bool diversify;
  };
  std::vector<unsigned> attempts;
  std::vector<size_t> failed_at;
  std::vector<bool> failed;
  long refreshes = 0, eligible = 0, cyclic_nodes = 0, cyclic_tasks = 0;
  long attempts_total = 0, successes = 0, geometric_failures = 0;
  long conditional_failures = 0, off_root_attempts = 0;
  long cycle_attempts = 0, imported_attempt_keys = 0;
  std::vector<int> cycle_vertices, return_distance;
  long diversification_attempts = 0, duplicate_rules = 0;
  long cycle_reachable_tasks = 0;

  void resize(size_t n) {
    attempts.resize(n);
    failed_at.resize(n);
    failed.resize(n);
  }
  void note(int node, bool success, bool geometric, size_t revision) {
    resize(std::max(attempts.size(), size_t(node + 1)));
    ++attempts[node];
    ++attempts_total;
    successes += success;
    geometric_failures += geometric;
    conditional_failures += !success && !geometric;
    failed[node] = !success;
    failed_at[node] = revision;
  }
  template <class Bank>
  std::vector<Task> rank(const Game &game, const Bank &bank,
                         const std::vector<bool> &blocked, bool cycles,
                         bool focus = false, bool diversify = false) {
    ++refreshes;
    int n = game.entries.size();
    size_t revision =
        bank.rules.size() + std::count(blocked.begin(), blocked.end(), true);
    resize(n);
    std::vector<int> viable(n);
    std::vector<bool> live(bank.rules.size());
    for (int i = 0; i < int(bank.rules.size()); ++i) {
      const auto &r = bank.rules[i];
      bool ok = !blocked[r.parent];
      for (int child : r.children)
        ok = ok && !blocked[child];
      live[i] = ok;
      viable[r.parent] += ok;
    }
    // A vertex with no currently usable complete rule needs a new proposal.
    // A previously covered parent can become eligible after a child fails.
    std::vector<bool> frontier(n);
    eligible = 0;
    for (int i = 0; i < n; ++i) {
      frontier[i] = !blocked[i] && viable[i] == 0;
      eligible += frontier[i];
    }
    std::vector<bool> cyclic(n);
    std::vector<int> distance(n, -1);
    return_distance.assign(n, -1);
    cycle_vertices.clear();
    cyclic_nodes = 0;
    if (cycles) {
      std::vector<std::vector<int>> edges(n), reverse(n);
      std::vector<bool> self(n);
      for (int i = 0; i < int(bank.rules.size()); ++i)
        if (live[i] || (focus && !blocked[bank.rules[i].parent])) {
          const auto &r = bank.rules[i];
          for (int child : r.children) {
            if (blocked[child])
              continue;
            edges[r.parent].push_back(child);
            reverse[child].push_back(r.parent);
            self[r.parent] = self[r.parent] || child == r.parent;
          }
        }
      // Iterative Kosaraju: no recursion depth limit on large dictionaries.
      std::vector<bool> seen(n);
      std::vector<int> order;
      for (int start = 0; start < n; ++start)
        if (!seen[start]) {
          std::vector<std::pair<int, size_t>> stack{{start, 0}};
          seen[start] = true;
          while (!stack.empty()) {
            int v = stack.back().first;
            auto &pos = stack.back().second;
            if (pos == edges[v].size()) {
              order.push_back(v);
              stack.pop_back();
            } else {
              int child = edges[v][pos++];
              if (!seen[child]) {
                seen[child] = true;
                stack.push_back({child, 0});
              }
            }
          }
        }
      std::fill(seen.begin(), seen.end(), false);
      for (auto it = order.rbegin(); it != order.rend(); ++it)
        if (!seen[*it]) {
          std::vector<int> component{*it};
          seen[*it] = true;
          for (size_t pos = 0; pos < component.size(); ++pos)
            for (int parent : reverse[component[pos]])
              if (!seen[parent]) {
                seen[parent] = true;
                component.push_back(parent);
              }
          for (int v : component)
            cyclic[v] = component.size() > 1 || self[v];
        }
      for (int i = 0; i < n; ++i)
        if (cyclic[i]) {
          ++cyclic_nodes;
          cycle_vertices.push_back(i);
        }
      if (focus) {
        std::deque<int> queue;
        for (int i : cycle_vertices) {
          distance[i] = 0;
          queue.push_back(i);
        }
        while (!queue.empty()) {
          int v = queue.front();
          queue.pop_front();
          for (int child : edges[v])
            if (distance[child] < 0) {
              distance[child] = distance[v] + 1;
              queue.push_back(child);
            }
        }
        for (int i : cycle_vertices) {
          return_distance[i] = 0;
          queue.push_back(i);
        }
        while (!queue.empty()) {
          int v = queue.front();
          queue.pop_front();
          for (int parent : reverse[v])
            if (return_distance[parent] < 0) {
              return_distance[parent] = return_distance[v] + 1;
              queue.push_back(parent);
            }
        }
      }
    }
    std::vector<double> credit(n);
    std::vector<int> references(n), single(n), cycle_refs(n);
    for (int i = 0; i < int(bank.rules.size()); ++i)
      if (live[i]) {
        const auto &r = bank.rules[i];
        int missing = 0;
        for (int child : r.children)
          missing += frontier[child];
        if (!missing)
          continue;
        // Share each parent's unit budget among its alternatives, and prefer
        // complete rules with fewer direct frontier obligations still missing.
        double value =
            (cyclic[r.parent] ? 8. : 1.) /
            (std::max(1, viable[r.parent]) * double(missing) * missing);
        for (int child : r.children)
          if (frontier[child]) {
            credit[child] += value;
            ++references[child];
            single[child] += missing == 1;
            cycle_refs[child] += cyclic[r.parent];
          }
      }
    std::vector<Task> tasks;
    cyclic_tasks = 0;
    cycle_reachable_tasks = 0;
    for (int i = 0; i < n; ++i)
      if (frontier[i] ||
          (diversify && !blocked[i] && return_distance[i] >= 0)) {
        // A geometric planner failure may become repairable after discovering
        // more rules. Do not retry it with an entirely unchanged rule bank.
        if (failed[i] && failed_at[i] == revision)
          continue;
        double score =
            (credit[i] + 1e-6) / std::pow(2., std::min(attempts[i], 16u));
        if (focus && distance[i] >= 0)
          score = (1 + credit[i]) / std::pow(1. + distance[i], 2) /
                  std::pow(2., std::min(attempts[i], 16u));
        bool alternative = !frontier[i];
        if (alternative)
          score = .5 / std::pow(1. + return_distance[i], 2) /
                  std::pow(2., std::min(attempts[i], 16u));
        tasks.push_back({i, score, references[i], single[i], cycle_refs[i],
                         alternative ? 0 : distance[i], alternative});
        cycle_reachable_tasks += distance[i] >= 0;
        cyclic_tasks += cycle_refs[i] > 0;
      }
    std::sort(tasks.begin(), tasks.end(),
              [focus](const Task &a, const Task &b) {
                if (focus && (a.cycle_distance >= 0) != (b.cycle_distance >= 0))
                  return a.cycle_distance >= 0;
                return a.score != b.score ? a.score > b.score : a.node < b.node;
              });
    return tasks;
  }
};
