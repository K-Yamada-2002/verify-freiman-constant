#define KF131_BLOCK_LIBRARY
#include "block_type_search.cpp"
#include <cassert>

int main() {
  memory = 3;
  minimum_shape_memory = 2;
  bins = 72;
  base = .96;
  menu = 1;
  ratio_max_depth = 2;
  prepare_catalog();
  int s = shape_lookup.at("222"), q = 20;
  int cid = lazy_cell(s, s, 1, q);
  BlockGame game({cid, 0, 1});
  auto coarse_dead = [](const Block &key) {
    int id = get<0>(key);
    int qi = id >= 0 ? cells[id].qi : get<3>(virtual_boxes[-1 - id]);
    return ratio_key(qi).level == 0;
  };
  double mid = (qb[q].lo + qb[q].hi) / 2;
  vector<Block> low;
  assert(choose_piece(cid, 0, 1, coarse_dead, game, false, low,
                      {qb[q].lo, mid - (mid - qb[q].lo) / 4}));
  assert(low.size() == 1);
  auto descriptor_q = [](Block key) {
    int id = get<0>(key);
    return id >= 0 ? cells[id].qi : get<3>(virtual_boxes[-1 - id]);
  };
  auto key = ratio_key(descriptor_q(low[0]));
  assert(key.bin == q && key.level == 1 && key.index == 0);
  vector<Block> all;
  assert(choose_piece(cid, 0, 1, coarse_dead, game, false, all, qb[q]));
  assert(all.size() == 2);
  auto left = qb[descriptor_q(all[0])], right = qb[descriptor_q(all[1])];
  assert(left.lo == qb[q].lo && left.hi == right.lo && right.hi == qb[q].hi);
  auto never = [](const Block &) { return true; };
  vector<Block> refused;
  assert(!choose_piece(cid, 0, 1, never, game, false, refused, qb[q]));
  assert(refused.empty());
  int lc = lazy_cell(s, s, 1, ratio_half(q, 0));
  int rc = lazy_cell(s, s, 1, ratio_half(q, 1));
  BlockGame bank({lc, 0, 1});
  bank.start_root({rc, 0, 1});
  existing_blocks[lc].insert({0, bank.ids.at({lc, 0, 1})});
  existing_blocks[rc].insert({0, bank.ids.at({rc, 0, 1})});
  probing = true;
  auto alive = [](const Block &) { return false; };
  auto joined = known_blocks(cid, bank, alive, qb[q]);
  assert((joined.domain == BlockDomain{{0, 1}}));
  assert(known_chain(joined, 0, 1).size() == 2);
  auto upper_missing = [&](const Block &key) { return get<0>(key) == rc; };
  assert(known_blocks(cid, bank, upper_missing, qb[q]).domain.empty());
  auto lower_only = known_blocks(cid, bank, upper_missing, {qb[q].lo, mid});
  assert(known_chain(lower_only, 0, 1).size() == 1);
  cout << "ratio clipping, mandatory halves, and atomic failure checked\n";
}
