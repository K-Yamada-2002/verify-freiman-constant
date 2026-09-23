// Floating-point proposal geometry. All accepted certificates are replayed
// independently by scalar_geometry.py over the exact number field.
#pragma once
Bounds discovery_quadratic(string w, double k, Bounds rb) {
  auto m = mat(w);
  double d = m[2] * anchor + m[3], z = phi(w, anchor);
  if (w.find_first_not_of('2') == string::npos)
    z = anchor;
  auto t = [&](double r) { return (1 + r * anchor) / (1 + r * z); };
  double t0 = min(t(rb.lo), t(rb.hi)), t1 = max(t(rb.lo), t(rb.hi));
  double a = k / (d * d), b = z - anchor;
  auto f = [&](double x) { return (a * x + b) * x; };
  Bounds out{min(f(t0), f(t1)), max(f(t0), f(t1))};
  if (a != 0) {
    double critical = -b / (2 * a);
    if (t0 < critical && critical < t1) {
      out.lo = min(out.lo, f(critical));
      out.hi = max(out.hi, f(critical));
    }
  }
  return out;
}
Bounds discovery_endpoint(const Cell &c, const Move &m, bool sw, int k) {
  double endpoint = double(k) / atlas_grid;
  auto l = discovery_quadratic(
      m.u, sw ? 0 : (m.u.size() % 2 ? -endpoint : endpoint), c.r);
  auto r = discovery_quadratic(
      m.v, sw ? (m.v.size() % 2 ? -endpoint : endpoint) : 0, c.sb);
  if (c.p < 0)
    r = {-r.hi, -r.lo};
  return {l.lo + min(c.q.lo * r.lo, c.q.hi * r.lo),
          l.hi + max(c.q.lo * r.hi, c.q.hi * r.hi)};
}
Bounds discovery_core(const Cell &c, const Move &m, bool sw, int lo, int hi) {
  bool positive =
      (sw ? c.p * (m.v.size() % 2 ? -1 : 1) : (m.u.size() % 2 ? -1 : 1)) > 0;
  return {discovery_endpoint(c, m, sw, positive ? lo : hi).hi,
          discovery_endpoint(c, m, sw, positive ? hi : lo).lo};
}
// Starting from a valid interval avoids computing an unnecessarily wide
// inverse hull when only a small part of a known child component is needed.
pair<int, int> discovery_trim(const Cell &c, const Move &m, bool sw,
                              pair<int, int> range, double lo, double hi) {
  int a = range.first, b = range.second - 1;
  while (a < b) {
    int mid = a + (b - a + 1) / 2;
    auto trial = discovery_core(c, m, sw, mid, range.second);
    if (trial.lo <= lo + 1e-13 && trial.hi >= hi - 1e-13)
      a = mid;
    else
      b = mid - 1;
  }
  range.first = a;
  a = range.first + 1;
  b = range.second;
  while (a < b) {
    int mid = a + (b - a) / 2;
    auto trial = discovery_core(c, m, sw, range.first, mid);
    if (trial.lo <= lo + 1e-13 && trial.hi >= hi - 1e-13)
      b = mid;
    else
      a = mid + 1;
  }
  range.second = a;
  return range;
}
pair<int, int> discovery_preimage(const Cell &c, const Move &m, bool sw,
                                  double lo, double hi, bool tighten) {
  auto range = atlas_preimage_interval(c, m, sw, lo, hi);
  if (!tighten || range.second <= range.first)
    return range;
  auto core = discovery_core(c, m, sw, range.first, range.second);
  if (core.lo > double(lo) / atlas_grid + 1e-13 ||
      core.hi < double(hi) / atlas_grid - 1e-13)
    return {0, 0};
  // Preserve shift/gain correlation by evaluating the complete quadratic
  // endpoint expression, then trimming the conservative inverse interval.
  return discovery_trim(c, m, sw, range, lo / atlas_grid, hi / atlas_grid);
}
