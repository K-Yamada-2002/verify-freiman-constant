// Alternating finite closure and targeted dictionary expansion.
#define KF131_BLOCK_LIBRARY
#include "block_type_search.cpp"
#include "feedback_registry.hpp"
#include "feedback_frontier.hpp"
#include "point_sieve.hpp"
#include "realize_type_seed.hpp"
#include "feedback_learning.hpp"
#include "alternative_cover_game.hpp"
#include "global_frontier.hpp"

int main(int argc, char **argv) {
  if (argc < 26) {
    cerr << "use lazy_type_search.py --method feedback\n";
    return 2;
  }
  menu = 1;
  memory = stoi(argv[2]);
  bins = stoi(argv[3]);
  base = stod(argv[4]);
  maxstep = stoi(argv[5]);
  string output = argv[6];
  int node_limit = stoi(argv[7]);
  outer_depth = stoi(argv[9]);
  membership_samples = stoi(argv[10]);
  root_trials = stoi(argv[12]);
  root_step_budget = stol(argv[13]);
  max_cells = stoi(argv[14]);
  seconds_limit = stod(argv[15]);
  atlas_grid = stoi(argv[19]);
  box_penalty = stoi(argv[20]);
  minimum_shape_memory = stoi(argv[21]);
  entry_depth = stoi(argv[22]);
  entry_samples = stoi(argv[23]);
  root_left = argv[24];
  root_right = argv[25];
  block_span = argc > 26 ? stoi(argv[26]) : 32;
  tight_preimages = argc > 27 ? stoi(argv[27]) != 0 : true;
  probe_percent = argc > 28 ? stoi(argv[28]) : 20;
  block_scheduler = argc > 29 ? stoi(argv[29]) : 0;
  subgrid_depth = argc > 30 ? stoi(argv[30]) : 0;
  if (memory < 2 || memory > 8 || bins < 1 || base <= 0 || base >= 1 ||
      maxstep < 1 || maxstep > 6 || outer_depth < 1 || outer_depth > 7 ||
      entry_depth < outer_depth || entry_depth > 7 || atlas_grid < 1 ||
      atlas_grid > 10000000 || max_cells < 1 || node_limit < 1 ||
      root_trials < 1 || root_step_budget < 1 || seconds_limit <= 0 ||
      block_span < 1 || block_span > 4096 || box_penalty < 0 ||
      probe_percent < 0 || probe_percent > 80 || block_scheduler < 0 ||
      block_scheduler > 2 || subgrid_depth < 0 || subgrid_depth > 6 ||
      (minimum_shape_memory &&
       (minimum_shape_memory < 2 || minimum_shape_memory > memory)))
    return 2;
  for (int n : {membership_samples, entry_samples})
    if (n != 1 && n != 3 && n != 11)
      return 2;
  for (const auto &w : {root_left, root_right})
    if (w.size() <= size_t(memory) || w.size() > 64 ||
        w.find_first_not_of("123") != string::npos || state(w) < 0)
      return 2;
  auto weight = [](string w) {
    auto m = mat(w);
    return m[2] * anchor + m[3];
  };
  if (weight(root_left) > weight(root_right))
    swap(root_left, root_right);
  double ratio = pow(weight(root_left) / weight(root_right), 2);
  prepare_catalog();
  int ls = shape_lookup.at(root_left.substr(root_left.size() - memory));
  int rs = shape_lookup.at(root_right.substr(root_right.size() - memory)),
      qi = -1;
  for (int i = 0; i < bins; ++i)
    if (qb[i].lo <= ratio && ratio <= qb[i].hi)
      qi = i;
  if (qi < 0)
    return 2;
  int root = lazy_cell(ls, rs,
                       (root_left.size() + root_right.size()) % 2 ? -1 : 1, qi);
  auto lm = mat(root_left), rm = mat(root_right);
  bool resuming = argc > 38 && string(argv[38]) != "-";
  if (!resuming && !(cells[root].r.lo <= lm[2] / lm[3] &&
                     lm[2] / lm[3] <= cells[root].r.hi &&
                     cells[root].sb.lo <= rm[2] / rm[3] &&
                     rm[2] / rm[3] <= cells[root].sb.hi))
    return 2;

  int round_steps = argc > 31 ? stoi(argv[31]) : 5000;
  int expansion_limit = argc > 32 ? stoi(argv[32]) : 2048;
  double round_seconds = argc > 33 ? stod(argv[33]) : 10;
  int repair_mode = argc > 34 ? stoi(argv[34]) : 1;
  sieve_depth = argc > 35 ? stoi(argv[35]) : 0;
  sieve_points = argc > 36 ? stoi(argv[36]) : 5;
  trim_known_ranges = argc > 37 ? stoi(argv[37]) != 0 : true;
  ratio_max_depth = argc > 39 ? stoi(argv[39]) : 0;
  ratio_clip_first = argc > 40 ? stoi(argv[40]) != 0 : true;
  direct_hull_filter = argc > 41 ? stoi(argv[41]) != 0 : true;
  cache_piece_estimates = argc > 42 ? stoi(argv[42]) != 0 : false;
  if (repair_mode < 0 || repair_mode > 1 || sieve_depth < 0 ||
      sieve_depth > 11 || sieve_points < 2 || sieve_points > 33 ||
      ratio_max_depth < 0 || ratio_max_depth > 8)
    return 2;
  if (round_steps < 1 || expansion_limit < 1 || round_seconds <= 0)
    return 2;
  FeedbackRegistry<BlockGame> registry(BlockGame::Entry{{root, 0, 1}});
  AlternativeCoverGame<BlockGame> alternatives;
  bool retain_alternatives = argc > 45 ? stoi(argv[45]) != 0 : false;
  long alternative_checks = 0, alternative_supported = 0;
  bool reuse_alternatives =
      retain_alternatives && (argc <= 46 || stoi(argv[46]) != 0);
  long retained_rule_reuses = 0;
  int global_mode = argc > 47 ? stoi(argv[47]) : 0;
  int global_batch = argc > 48 ? stoi(argv[48]) : 512;
  if (global_mode < 0 || global_mode > 4 || global_batch < 1 ||
      (global_mode && !retain_alternatives))
    return 2;
  double return_penalty = argc > 50 ? stod(argv[50]) : 32;
  if (!isfinite(return_penalty) || return_penalty < 0)
    return 2;
  GlobalFrontier<BlockGame> global_frontier;
  if (retain_alternatives) {
    registry.on_install = [&](const BlockGame &game, int id) {
      alternatives.record(game, id);
    };
    write_catalog_extra = [&](ostream &out, const BlockGame &game,
                              const map<int, int> &index) {
      out << ",\"alternative_rules\":[";
      for (size_t i = 0; i < alternatives.rules.size(); ++i) {
        if (i)
          out << ',';
        const auto &rule = alternatives.rules[i];
        out << "{\"parent\":" << index.at(rule.parent) << ",\"children\":[";
        write_block_edges(out, rule.plan, get<0>(game.entries[rule.parent].key),
                          index, game);
        out << "]}";
      }
      out << ']';
    };
  }
  if (resuming) {
    // The saved root may use a shorter, valid suffix box than the new
    // refinement limit. The importer validates that actual saved seed.
    import_feedback_frontier(registry, argv[38], node_limit);
    root = get<0>(registry.game.entries[registry.game.root_id].key);
  }
  auto &catalog = registry.game;
  FeedbackLearning learning;
  learning.weight = argc > 43 ? stod(argv[43]) : 0;
  if (!isfinite(learning.weight) || learning.weight < 0)
    return 2;
  if (argc > 44 && string(argv[44]) != "-")
    learning.load(argv[44]);
  if (argc > 49 && string(argv[49]) != "-") {
    FeedbackLearning prior_attempts;
    prior_attempts.load(argv[49]);
    global_frontier.resize(catalog.entries.size());
    for (auto [key, count] : prior_attempts.failures) {
      auto found = catalog.ids.find(key);
      if (found != catalog.ids.end()) {
        global_frontier.attempts[found->second] =
            min(count, long(numeric_limits<unsigned>::max()));
        ++global_frontier.imported_attempt_keys;
      }
    }
  }
  if (learning.weight > 0 || global_mode == 4)
    learned_block_cost = [&](const Block &key) {
      double value = learning.cost(key, catalog);
      if (global_mode == 4 && global_frontier.cyclic_nodes) {
        Block resolved = key;
        if (get<0>(resolved) < 0)
          get<0>(resolved) = peek_cell(get<0>(resolved));
        auto found = catalog.ids.find(resolved);
        bool returns =
            found != catalog.ids.end() &&
            size_t(found->second) < global_frontier.return_distance.size() &&
            global_frontier.return_distance[found->second] >= 0;
        if (!returns)
          value += return_penalty;
      }
      return value;
    };
  unique_ptr<BlockGame> probe;
  map<Block, BlockGame::Proposal> repairs;
  set<Block> impossible;
  auto recover_alternatives = [&]() {
    if (!retain_alternatives)
      return;
    vector<bool> blocked(catalog.entries.size());
    for (const auto &key : impossible) {
      auto found = catalog.ids.find(key);
      if (found != catalog.ids.end())
        blocked[found->second] = true;
    }
    auto core = alternatives.supported(catalog.entries.size(), blocked);
    ++alternative_checks;
    alternative_supported = core.nodes.size();
    if (!core.nodes.empty()) {
      alternatives.materialize(catalog, core);
      catalog.closed = catalog.closure();
      if (!catalog.closed && elapsed() < seconds_limit)
        salvage_supported_seed(catalog);
    }
  };
  vector<array<long, 9>> history;
  int trial = 0;
  long rounds = 0, expansions = 0, total_probe_steps = 0, total_failed = 0;
  long total_repairs = 0, peak_repair_frontier = 0;
  long repairs_avoiding_failed = 0, repairs_with_fallback = 0;
  size_t frozen_size = 0;
  bool limit_hit = false;
  auto write_history = [&](bool finished) {
    ofstream log(output + ".feedback.json.tmp");
    learning.save(output + ".learning.txt");
    if (global_mode) {
      FeedbackLearning attempts;
      for (size_t i = 0; i < global_frontier.attempts.size(); ++i)
        if (global_frontier.attempts[i])
          attempts.failures[catalog.entries[i].key] =
              global_frontier.attempts[i];
      attempts.save(output + ".global.txt");
    }
    log << "{\"global_mode\":" << global_mode
        << ",\"global_attempts\":" << global_frontier.attempts_total
        << ",\"global_successes\":" << global_frontier.successes
        << ",\"global_geometric_failures\":"
        << global_frontier.geometric_failures
        << ",\"global_conditional_failures\":"
        << global_frontier.conditional_failures
        << ",\"global_off_root_attempts\":" << global_frontier.off_root_attempts
        << ",\"global_cycle_attempts\":" << global_frontier.cycle_attempts
        << ",\"global_cycle_reachable_tasks\":"
        << global_frontier.cycle_reachable_tasks
        << ",\"global_imported_attempt_keys\":"
        << global_frontier.imported_attempt_keys
        << ",\"global_diversification_attempts\":"
        << global_frontier.diversification_attempts
        << ",\"global_duplicate_rules\":" << global_frontier.duplicate_rules
        << ",\"return_penalty\":" << return_penalty
        << ",\"global_eligible\":" << global_frontier.eligible
        << ",\"global_cyclic_nodes\":" << global_frontier.cyclic_nodes
        << ",\"global_cyclic_tasks\":" << global_frontier.cyclic_tasks
        << ",\"learning_weight\":" << learning.weight
        << ",\"conditional_failure_observations\":" << learning.observations
        << ",\"repeated_conditional_failures\":" << learning.repeated
        << ",\"distinct_conditional_failures\":" << learning.failures.size()
        << ",\"unchanged_repair_dependencies\":" << learning.same_repairs
        << ",\"changed_repair_dependencies\":" << learning.changed_repairs
        << ",\"imported_learning_keys\":" << learning.imported
        << ",\"weighted_slice_queries\":" << weighted_slice_queries
        << ",\"weighted_edge_queries\":" << weighted_edge_queries
        << ",\"retained_rule_reuses\":" << retained_rule_reuses
        << ",\"retained_alternative_rules\":" << alternatives.rules.size()
        << ",\"alternative_fixed_point_checks\":" << alternative_checks
        << ",\"alternative_supported_nodes\":" << alternative_supported
        << ",\"rounds\":[";
    for (size_t i = 0; i < history.size(); ++i) {
      if (i)
        log << ',';
      auto r = history[i];
      log << "{\"round\":" << r[0] << ",\"registered_before\":" << r[1]
          << ",\"probe_steps\":" << r[2] << ",\"probe_rejected\":" << r[3]
          << ",\"repair_candidates\":" << r[4]
          << ",\"installed_repairs\":" << r[5]
          << ",\"registered_after\":" << r[6] << ",\"reachable\":" << r[7]
          << ",\"open\":" << r[8] << '}';
    }
    log << "],\"total_probe_steps\":" << total_probe_steps
        << ",\"total_probe_rejections\":" << total_failed
        << ",\"installed_repairs\":" << total_repairs
        << ",\"new_types_from_repairs\":" << expansions
        << ",\"geometric_filter_rejections\":" << impossible.size()
        << ",\"peak_repair_frontier\":" << peak_repair_frontier
        << ",\"repairs_avoiding_failed\":" << repairs_avoiding_failed
        << ",\"repairs_with_fallback\":" << repairs_with_fallback
        << ",\"supported_nodes\":" << supported_node_count
        << ",\"supported_seed_checks\":" << supported_seed_checks
        << ",\"sieve_depth\":" << sieve_depth
        << ",\"sieve_queries\":" << sieve_queries
        << ",\"sieve_rejections\":" << sieve_rejections
        << ",\"trim_known_ranges\":" << (trim_known_ranges ? "true" : "false")
        << ",\"known_range_trims\":" << known_range_trims
        << ",\"known_range_atoms_removed\":" << known_range_atoms_removed
        << ",\"imported_types\":" << imported_types
        << ",\"imported_rules\":" << imported_rules
        << ",\"imported_alternatives\":" << imported_alternatives
        << ",\"ratio_max_depth\":" << ratio_max_depth
        << ",\"ratio_clip_first\":" << (ratio_clip_first ? "true" : "false")
        << ",\"ratio_clipped_requests\":" << ratio_clipped_requests
        << ",\"refined_ratio_bins\":" << refined_ratios.size()
        << ",\"ratio_split_attempts\":" << ratio_split_attempts
        << ",\"ratio_split_successes\":" << ratio_split_successes
        << ",\"piece_estimate_calls\":" << piece_estimate_calls
        << ",\"piece_estimate_cache_hits\":" << piece_estimate_hits
        << ",\"direct_hull_filter\":" << (direct_hull_filter ? "true" : "false")
        << ",\"direct_hull_queries\":" << direct_hull_queries
        << ",\"direct_hull_rejections\":" << direct_hull_rejections
        << ",\"piece_cache\":" << (cache_piece_estimates ? "true" : "false")
        << ",\"finished\":" << (finished ? "true" : "false") << "}\n";
    log.close();
    rename((output + ".feedback.json.tmp").c_str(),
           (output + ".feedback.json").c_str());
  };
  probing = true;
  tried_roots = 1;
  block_save(output, catalog, false);
  try {
    if (global_mode) {
      while (elapsed() < seconds_limit) {
        check_time();
        learning.refresh(catalog);
        vector<bool> blocked(catalog.entries.size());
        for (const auto &key : impossible) {
          auto it = catalog.ids.find(key);
          if (it != catalog.ids.end())
            blocked[it->second] = true;
        }
        auto tasks = global_frontier.rank(catalog, alternatives, blocked,
                                          global_mode >= 2, global_mode >= 3,
                                          global_mode == 4);
        vector<bool> reached_before(catalog.entries.size());
        for (int i : catalog.reachable())
          reached_before[i] = true;
        if (tasks.empty()) {
          stop_reason = "global frontier exhausted at current rule bank";
          break;
        }
        ++rounds;
        size_t before = catalog.entries.size();
        long installed = 0, attempted = 0;
        double deadline = min(seconds_limit, elapsed() + round_seconds);
        auto hard_dead = [&](const Block &key) {
          return impossible.count(key);
        };
        for (const auto &task : tasks) {
          if (attempted >= global_batch || elapsed() >= deadline)
            break;
          check_time();
          int id = task.node;
          Block key = catalog.entries[id].key;
          ++attempted;
          global_frontier.off_root_attempts += !reached_before[id];
          global_frontier.cycle_attempts +=
              task.cycle_distance >= 0 || task.cyclic_references > 0;
          if (!feedback_sieve(key) || !block_available(key, false) ||
              !block_available(key, true)) {
            impossible.insert(key);
            registry.withdraw(key);
            global_frontier.note(id, false, true,
                                 alternatives.rules.size() + impossible.size());
            continue;
          }
          optional<Block> excluded;
          if (task.diversify) {
            ++global_frontier.diversification_attempts;
            vector<int> escapes;
            for (int child : catalog.entries[id].children)
              if (size_t(child) >= global_frontier.return_distance.size() ||
                  global_frontier.return_distance[child] < 0)
                escapes.push_back(child);
            if (escapes.empty())
              escapes = catalog.entries[id].children;
            if (!escapes.empty())
              excluded = catalog
                             .entries[escapes[global_frontier.attempts[id] %
                                              escapes.size()]]
                             .key;
          }
          auto discovery_dead = [&](const Block &child) {
            return hard_dead(child) || (excluded && child == *excluded);
          };
          auto proposal = block_proposal(key, catalog, discovery_dead);
          if (!proposal) {
            learning.failed(key);
            global_frontier.note(id, false, false,
                                 alternatives.rules.size() + impossible.size());
            continue;
          }
          size_t old_rules = alternatives.rules.size();
          if (!registry.install(key, *proposal, node_limit)) {
            limit_hit = true;
            break;
          }
          learning.repair(key, proposal->children);
          if (alternatives.rules.size() == old_rules) {
            ++global_frontier.duplicate_rules;
            global_frontier.note(id, false, false,
                                 alternatives.rules.size() + impossible.size());
            continue;
          }
          global_frontier.note(id, true, false,
                               alternatives.rules.size() + impossible.size());
          ++installed;
        }
        total_repairs += installed;
        expansions += catalog.entries.size() - before;
        recover_alternatives();
        auto reached = catalog.reachable();
        long open = 0;
        for (int id : reached)
          open += catalog.entries[id].status != BlockGame::Local;
        history.push_back({rounds, long(before), attempted, 0, 0, installed,
                           long(catalog.entries.size()), long(reached.size()),
                           open});
        if (elapsed() - last_checkpoint > 10 || rounds < 4 || catalog.closed) {
          block_save(output, catalog, false);
          write_history(false);
          cerr << "global round " << rounds << " types "
               << catalog.entries.size() << " attempted " << attempted
               << " installed " << installed << " eligible "
               << global_frontier.eligible << " cycle frontier "
               << global_frontier.cyclic_tasks << '\n';
        }
        if (catalog.closed || limit_hit)
          break;
      }
      if (!catalog.closed)
        stop_reason =
            limit_hit ? "global registered type limit"
                      : (elapsed() >= seconds_limit ? "global wall clock limit"
                                                    : stop_reason);
    } else
      while (elapsed() < seconds_limit && trial < root_trials) {
        check_time();
        Block seed = catalog.entries[catalog.root_id].key;
        if (!probe) {
          frozen_size = catalog.entries.size();
          probe = make_unique<BlockGame>(seed, block_scheduler == 0);
          probe->prefer_shared = block_scheduler == 2;
          repairs.clear();
        } else if (frozen_size != catalog.entries.size()) {
          frozen_size = catalog.entries.size();
          probe->reconsider_rejections(seed);
          repairs.clear();
        } else {
          probe->start_root(
              seed); // Reactivate a task interrupted by a soft clock limit.
        }
        learning.refresh(catalog);
        ++rounds;
        double deadline = min(seconds_limit, elapsed() + round_seconds);
        long old_steps = probe->steps, old_rejected = probe->rejected;
        bool interrupted = false;
        auto hard_dead = [&](const Block &key) {
          return impossible.count(key);
        };
        auto planner = [&](const Block &key,
                           const auto &dead) -> optional<BlockGame::Proposal> {
          check_time();
          if (elapsed() >= deadline)
            throw SearchLimit("feedback round clock");
          if (!feedback_sieve(key)) {
            impossible.insert(key);
            registry.withdraw(key);
            return nullopt;
          }
          auto forbidden = [&](const Block &child) {
            auto found = catalog.ids.find(child);
            return found == catalog.ids.end() ||
                   size_t(found->second) >= frozen_size ||
                   impossible.count(child) || dead(child);
          };
          optional<BlockGame::Proposal> proposal;
          auto stored = catalog.ids.find(key);
          if (reuse_alternatives && stored != catalog.ids.end()) {
            proposal = alternatives.propose(
                catalog, stored->second,
                [&](int id) { return forbidden(catalog.entries[id].key); },
                [&](int id) {
                  return learning.weight > 0
                             ? learning.cost(catalog.entries[id].key, catalog)
                             : double(catalog.entries[id].status !=
                                      BlockGame::Local);
                });
            retained_rule_reuses += bool(proposal);
          }
          if (!proposal)
            proposal = block_proposal(key, catalog, forbidden);
          if (proposal) {
            if (!registry.install(key, *proposal, node_limit))
              throw logic_error("restricted rule escaped frozen dictionary");
            repairs.erase(key);
            return proposal;
          }
          if (!block_available(key, false) || !block_available(key, true)) {
            impossible.insert(key);
            registry.withdraw(key);
            return nullopt;
          }
          learning.failed(key);
          // Failure in a fixed dictionary is not a geometric impossibility.
          // Find a complete repair before choosing which new types to add.
          auto avoid_failed = [&](const Block &child) {
            return hard_dead(child) || dead(child);
          };
          auto repair = block_proposal(
              key, catalog,
              repair_mode ? function<bool(const Block &)>(avoid_failed)
                          : function<bool(const Block &)>(hard_dead));
          if (repair && repair_mode)
            ++repairs_avoiding_failed;
          if (!repair && repair_mode) {
            repair = block_proposal(key, catalog, hard_dead);
            repairs_with_fallback += bool(repair);
          }
          if (repair) {
            learning.repair(key, repair->children);
            repairs[key] = move(*repair);
          }
          return nullopt;
        };
        try {
          probe->run(planner, frozen_size, probe->steps + round_steps);
        } catch (const SearchLimit &error) {
          interrupted = true;
        }
        total_probe_steps += probe->steps - old_steps;
        total_failed += probe->rejected - old_rejected;
        catalog.steps = total_probe_steps;
        probe_steps = total_probe_steps;
        probe_rejections = total_failed;
        peak_repair_frontier = max(peak_repair_frontier, long(repairs.size()));
        if (elapsed() >= seconds_limit) {
          stop_reason = "wall clock limit";
          break;
        }
        if (probe->closed) {
          for (int id : probe->reachable()) {
            const auto &entry = probe->entries[id];
            BlockGame::Proposal final_plan{entry.plan, {}};
            for (int child : entry.children)
              final_plan.children.push_back(probe->entries[child].key);
            if (!registry.install(entry.key, final_plan, node_limit))
              throw logic_error("closed probe installation exceeded catalog");
          }
          catalog.root_id = catalog.ids.at(probe->entries[probe->root_id].key);
          catalog.closed = catalog.closure();
          probe_closed = true;
          stop_reason =
              "feedback finite closure candidate requires exact replay";
          break;
        }
        // Follow only the current root's failed proof dependencies. Installing
        // one repair is atomic: all its mandatory children enter the catalog.
        vector<Block> queue{seed};
        set<Block> seen{seed};
        long installed = 0;
        for (size_t i = 0; i < queue.size(); ++i) {
          check_time();
          const Block key = queue[i];
          auto repair = repairs.find(key);
          if (repair != repairs.end() &&
              catalog.entries.size() - frozen_size < size_t(expansion_limit)) {
            if (!registry.install(key, repair->second, node_limit)) {
              limit_hit = true;
              break;
            }
            ++installed;
          }
          auto found = catalog.ids.find(key);
          if (found == catalog.ids.end())
            continue;
          for (int child : catalog.entries[found->second].children) {
            const Block &next = catalog.entries[child].key;
            if (seen.insert(next).second)
              queue.push_back(next);
          }
        }
        total_repairs += installed;
        expansions += catalog.entries.size() - frozen_size;
        catalog.closed = catalog.closure();
        auto reached = catalog.reachable();
        long open = 0;
        for (int i : reached)
          open += catalog.entries[i].status != BlockGame::Local;
        history.push_back({rounds, long(frozen_size), probe->steps - old_steps,
                           probe->rejected - old_rejected, long(repairs.size()),
                           installed, long(catalog.entries.size()),
                           long(reached.size()), open});
        if (elapsed() - last_checkpoint > 10 || rounds < 4 || catalog.closed) {
          if (!catalog.closed)
            recover_alternatives();
          if (!catalog.closed)
            salvage_supported_seed(catalog);
          block_save(output, catalog, false);
          write_history(false);
          cerr << "feedback round " << rounds << " types "
               << catalog.entries.size() << " reachable " << reached.size()
               << " open " << open << " repairs " << installed << '\n';
        }
        if (catalog.closed) {
          stop_reason =
              "feedback repairs closed a candidate requiring exact replay";
          break;
        }
        if (limit_hit) {
          stop_reason = "registered type limit";
          break;
        }
        if (catalog.entries.size() == frozen_size && !interrupted &&
            probe->entries[probe->root_id].status == BlockGame::Rejected) {
          ++trial;
          if (trial >= root_trials)
            break;
          int k = trial % 2 ? -(trial + 1) / 2 : trial / 2;
          if (catalog.entries.size() >= size_t(node_limit))
            break;
          catalog.root_id = registry.ensure(Block{root, k, k + 1});
          ++tried_roots;
        }
      }
  } catch (const SearchLimit &error) {
    stop_reason = error.what();
  }
  // The finite hypergraph pass has no geometry expansion and is also run
  // after a clock limit, so the final saved alternatives are all considered.
  recover_alternatives();
  if (!catalog.closed && elapsed() < seconds_limit)
    salvage_supported_seed(catalog);
  probing = false;
  catalog.closed = catalog.closure();
  catalog.steps = total_probe_steps;
  block_save(output, catalog, true);
  write_history(true);
  block_save(output + ".catalog.json", catalog, true, true);
  cerr << "finished feedback: " << stop_reason << " closed=" << catalog.closed
       << '\n';
}
