#define KF131_BLOCK_LIBRARY
#include "block_type_search.cpp"
#include "feedback_registry.hpp"
#include "feedback_learning.hpp"
#include <cassert>
int main(int argc, char **argv) {
  memory = 3;
  minimum_shape_memory = 2;
  bins = 72;
  base = .96;
  menu = 1;
  ratio_max_depth = 2;
  prepare_catalog();
  int s = shape_lookup.at("222"), c = lazy_cell(s, s, 1, ratio_half(20, 0));
  Block a{c, 0, 1}, b{c, 1, 2}, d{c, 2, 3};
  FeedbackRegistry<BlockGame> registry(BlockGame::Entry{a});
  registry.install(a, {{}, {b}}, 100);
  registry.install(b, {{}, {d}}, 100);
  auto &game = registry.game;
  FeedbackLearning learning;
  learning.weight = 8;
  learning.refresh(game);
  assert(learning.cost(a, game) > 0 &&
         learning.cost(a, game) < learning.cost(b, game));
  double before = learning.cost(a, game);
  learning.failed(a);
  learning.failed(a);
  assert(learning.repeated == 1 && learning.cost(a, game) > before);
  learning.repair(a, {b});
  learning.repair(a, {b});
  learning.repair(a, {d});
  assert(learning.same_repairs == 1 && learning.changed_repairs == 1);
  registry.install(d, {{}, {a}}, 100);
  learning.refresh(game);
  assert(game.closure() && learning.cost(b, game) == 0);
  // Histories rank alternatives without invalidating a legitimate cycle.
  assert(game.supported_nodes().size() == 3 && learning.cost(a, game) > 0);
  assert(argc == 2);
  learning.save(argv[1]);
  FeedbackLearning restored;
  restored.weight = 8;
  restored.load(argv[1]);
  restored.refresh(game);
  assert(restored.failures == learning.failures &&
         restored.cost(a, game) == learning.cost(a, game));
  atlas_grid *= 2;
  bool refused = false;
  try {
    restored.load(argv[1]);
  } catch (const runtime_error &) {
    refused = true;
  }
  assert(refused);
  cout << "failure ranking, open descendants, cycles, persistent history "
          "passed\n";
}
