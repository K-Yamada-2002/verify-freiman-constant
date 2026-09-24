// This catalog stores immutable interval types and provisional geometric
// rules. Its work queue is never used; finite-domain probes own their queues
// and rejection sets. Installing a rule registers EVERY child together.
#pragma once
#include <cstddef>
#include <functional>
#include <set>
#include <utility>
#include <vector>

template <class Game> class FeedbackRegistry {
public:
  Game game;
  std::function<void(const Game &, int)> on_install;
  explicit FeedbackRegistry(const typename Game::Entry &root)
      : game(root.key) {}

  template <class Key> int ensure(const Key &key) {
    auto found = game.ids.find(key);
    if (found != game.ids.end())
      return found->second;
    int id = game.entries.size();
    game.ids[key] = id;
    game.entries.push_back({key, Game::Pending, {}, {}, {}, false});
    return id;
  }

  template <class Key> void withdraw(const Key &key) {
    auto found = game.ids.find(key);
    if (found == game.ids.end())
      return;
    int id = found->second;
    for (int child : game.entries[id].children)
      game.entries[child].parents.erase(id);
    auto &entry = game.entries[id];
    entry.children.clear();
    entry.plan = {};
    entry.status = Game::Pending;
  }

  template <class Key>
  bool install(const Key &key, const typename Game::Proposal &proposal,
               std::size_t limit) {
    std::set<Key> missing;
    if (!game.ids.count(key))
      missing.insert(key);
    for (const auto &child : proposal.children)
      if (!game.ids.count(child))
        missing.insert(child);
    if (game.entries.size() + missing.size() > limit)
      return false;
    int id = ensure(key);
    std::vector<int> children;
    for (const auto &child : proposal.children)
      children.push_back(ensure(child));
    for (int child : game.entries[id].children)
      game.entries[child].parents.erase(id);
    auto &entry = game.entries[id];
    entry.children = std::move(children);
    entry.plan = proposal.plan;
    entry.status = Game::Local;
    for (int child : entry.children)
      game.entries[child].parents.insert(id);
    if (on_install)
      on_install(game, id);
    return true;
  }
};
