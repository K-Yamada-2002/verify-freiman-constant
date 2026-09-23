// Dyadic subdivisions of a logarithmic base bin. Their exact definition is
// (base^(b+1) + k*(base^b-base^(b+1))/2^level), not a floating endpoint.
#pragma once
struct RatioKey {
  int bin, level, index;
};
int ratio_max_depth = 0;
bool ratio_clip_first = true;
long ratio_clipped_requests = 0;
long ratio_split_attempts = 0, ratio_split_successes = 0;
map<tuple<int, int, int>, int> ratio_ids;
vector<RatioKey> refined_ratios;
RatioKey ratio_key(int id) {
  if (id < bins)
    return {id, 0, 0};
  return refined_ratios.at(id - bins);
}
int ratio_id(int bin, int level, int index) {
  if (bin < 0 || bin >= bins || level < 0 || level > 16 || index < 0 ||
      index >= (1 << level))
    throw runtime_error("invalid dyadic ratio cell");
  if (!level)
    return bin;
  auto key = make_tuple(bin, level, index);
  auto old = ratio_ids.find(key);
  if (old != ratio_ids.end())
    return old->second;
  int id = qb.size();
  double width = ldexp(qb[bin].hi - qb[bin].lo, -level);
  qb.push_back({qb[bin].lo + index * width, qb[bin].lo + (index + 1) * width});
  refined_ratios.push_back({bin, level, index});
  ratio_ids[key] = id;
  return id;
}
int ratio_half(int id, int side) {
  auto key = ratio_key(id);
  return ratio_id(key.bin, key.level + 1, 2 * key.index + side);
}
