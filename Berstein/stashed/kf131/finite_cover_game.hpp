// A finite, lazy AND/OR search. Local plans are provisional until every
// reachable dependency also has a local plan. Rejection invalidates parents.
// Geometry and final proof verification deliberately live outside this file.
#pragma once
#include <algorithm>
#include <deque>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <vector>

template <class Key, class Plan> class FiniteCoverGame {
public:
  enum Status { Pending, Local, Rejected };
  struct Proposal {
    Plan plan;
    std::vector<Key> children;
  };
  struct Entry {
    Key key;
    Status status = Pending;
    Plan plan{};
    std::vector<int> children;
    std::set<int> parents;
    bool queued = true;
    long attempts = 0;
  };
  using Planner = std::function<std::optional<Proposal>(
      const Key &, const std::function<bool(const Key &)> &)>;
  std::vector<Entry> entries;
  std::map<Key, int> ids;
  int root_id = 0;
  long steps = 0, scheduled = 0, cancelled = 0, replans = 0, rejected = 0;
  bool limit_reached = false, node_limit_reached = false, closed = false;
  bool prefer_shared = false;

  explicit FiniteCoverGame(const Key &root, bool depth_first = false)
      : depth_first(depth_first) {
    add(root);
  }

  std::vector<int> reachable() const {
    std::vector<int> out{root_id};
    std::vector<bool> seen(entries.size());
    seen[root_id] = true;
    for (size_t i = 0; i < out.size(); ++i)
      for (int child : entries[out[i]].children)
        if (!seen[child]) {
          seen[child] = true;
          out.push_back(child);
        }
    return out;
  }

  bool closure() const {
    for (int i : reachable())
      if (entries[i].status != Local)
        return false;
    return true;
  }

  // Only for an explicitly enlarged candidate universe. Rejections may
  // have relied on missing alternatives; positive plans remain valid.
  void reconsider_rejections(const Key &root) {
    for (auto &entry : entries)
      if (entry.status == Rejected)
        entry.status = Pending;
    start_root(root);
  }

  void start_root(const Key &key) {
    for (int j : queue) {
      entries[j].queued = false;
      ++cancelled;
    }
    queue.clear();
    root_id = add(key);
    for (int j : reachable())
      if (entries[j].status == Pending && !entries[j].queued) {
        entries[j].queued = true;
        if (depth_first)
          queue.push_front(j);
        else
          queue.push_back(j);
        ++scheduled;
      }
    closed = false;
    limit_reached = false;
    node_limit_reached = false;
  }

  std::vector<int> supported_nodes() const {
    std::vector<bool> alive(entries.size());
    std::deque<int> failed;
    for (int i = 0; i < (int)entries.size(); ++i) {
      alive[i] = entries[i].status == Local;
      if (!alive[i])
        failed.push_back(i);
    }
    while (!failed.empty()) {
      int i = failed.front();
      failed.pop_front();
      for (int p : entries[i].parents)
        if (alive[p]) {
          alive[p] = false;
          failed.push_back(p);
        }
    }
    std::vector<int> out;
    for (int i = 0; i < (int)entries.size(); ++i)
      if (alive[i])
        out.push_back(i);
    return out;
  }

  void run(const Planner &planner, size_t node_limit, long step_limit) {
    if (entries[root_id].status == Rejected) {
      closed = false;
      return;
    }
    auto is_rejected = [&](const Key &key) {
      auto it = ids.find(key);
      return it != ids.end() && entries[it->second].status == Rejected;
    };
    while (!queue.empty() && steps < step_limit) {
      int i = queue.front();
      queue.pop_front();
      entries[i].queued = false;
      Key key = entries[i].key;
      ++steps;
      ++entries[i].attempts;
      auto proposal = planner(key, is_rejected);
      // Remove the old plan's reverse dependencies before installing a new
      // plan. Stale parents must never invalidate a later unrelated plan.
      for (int j : entries[i].children)
        entries[j].parents.erase(i);
      entries[i].children.clear();
      entries[i].plan = Plan{};
      if (!proposal) {
        entries[i].status = Rejected;
        ++rejected;
        auto parents = entries[i].parents;
        for (int parent : parents)
          if (entries[parent].status != Rejected) {
            entries[parent].status = Pending;
            if (!entries[parent].queued) {
              queue.push_front(parent);
              entries[parent].queued = true;
              ++scheduled;
              ++replans;
            }
          }
        if (entries[root_id].status == Rejected)
          break;
      } else {
        std::set<Key> missing;
        for (const auto &child : proposal->children)
          if (!ids.count(child))
            missing.insert(child);
        if (entries.size() + missing.size() > node_limit) {
          entries[i].status = Pending;
          limit_reached = true;
          node_limit_reached = true;
          break;
        }
        std::vector<int> children;
        for (const auto &child : proposal->children)
          children.push_back(add(child));
        entries[i].children = children;
        entries[i].plan = std::move(proposal->plan);
        entries[i].status = Local;
        for (int child : children)
          entries[child].parents.insert(i);
      }
      if (steps >= next_sweep || queue.empty()) {
        auto reached = reachable();
        bool all_local = true;
        for (int j : reached)
          all_local = all_local && entries[j].status == Local;
        if (all_local) {
          closed = true;
          return;
        }
        // Full graph scans every 128 steps become quadratic when the graph
        // has hundreds of thousands of nodes. Scale the interval with the
        // currently reached graph; queue exhaustion still forces a check.
        next_sweep =
            steps + std::max(128L, std::min(16384L, long(reached.size() / 8)));
        // Alternative plans can make old subtrees irrelevant. Suspend their
        // queued work, while retaining their types and rejection information.
        // add() reactivates a pending type if a later plan needs it again.
        std::set<int> active;
        for (int j : reached)
          active.insert(j);
        std::deque<int> retained;
        for (int j : queue)
          if (active.count(j))
            retained.push_back(j);
          else {
            entries[j].queued = false;
            ++cancelled;
          }
        queue.swap(retained);
        for (int j : active)
          if (entries[j].status == Pending && !entries[j].queued) {
            entries[j].queued = true;
            queue.push_back(j);
            ++scheduled;
          }
        if (prefer_shared)
          std::stable_sort(queue.begin(), queue.end(), [&](int a, int b) {
            if (entries[a].parents.size() != entries[b].parents.size())
              return entries[a].parents.size() > entries[b].parents.size();
            return a < b;
          });
      }
    }
    closed = closure();
    if (!queue.empty() && steps >= step_limit && !closed)
      limit_reached = true;
  }

private:
  long next_sweep = 128;
  bool depth_first;
  std::deque<int> queue;
  int add(const Key &key) {
    auto it = ids.find(key);
    if (it != ids.end()) {
      auto &entry = entries[it->second];
      if (entry.status == Pending && !entry.queued) {
        entry.queued = true;
        if (depth_first)
          queue.push_front(it->second);
        else
          queue.push_back(it->second);
        ++scheduled;
      }
      return it->second;
    }
    int i = entries.size();
    ids[key] = i;
    entries.push_back({key, Pending, Plan{}, {}, {}, true});
    if (depth_first)
      queue.push_front(i);
    else
      queue.push_back(i);
    ++scheduled;
    return i;
  }
};
