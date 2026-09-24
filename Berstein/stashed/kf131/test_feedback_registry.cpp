#include "feedback_registry.hpp"
#include "finite_cover_game.hpp"
#include <cassert>
#include <iostream>
using Game = FiniteCoverGame<int, int>;
int main() {
  FeedbackRegistry<Game> registry(Game::Entry{0});
  assert(!registry.install(0, Game::Proposal{0, {1, 2}}, 2));
  assert(registry.game.entries.size() == 1);
  assert(registry.install(0, Game::Proposal{0, {1, 2}}, 3));
  assert(registry.install(1, Game::Proposal{1, {1}}, 3));
  assert(!registry.game.closure()); // Mandatory sibling 2 remains open.
  assert(registry.install(2, Game::Proposal{2, {2}}, 3));
  assert(registry.game.closure());
  registry.withdraw(2);
  assert(!registry.game.closure());
  assert(registry.install(2, Game::Proposal{2, {2}}, 3));
  assert(registry.install(0, Game::Proposal{0, {1}}, 3));
  assert(!registry.game.entries[2].parents.count(0));
  assert(registry.game.entries[2].parents.count(2));
  assert(registry.game.reachable().size() == 2);
  std::cout << "feedback catalog atomic registration and dependency "
               "replacement passed\n";
}
