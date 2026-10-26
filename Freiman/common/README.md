# Shared arithmetic and proof helpers

These modules support the entry points in [verify/](../verify/README.md) and
[search/](../search/README.md). Their presence here does not mean that their
historical standalone search modes are additional proof obligations.

| Sources | Responsibility |
|---|---|
| [exact_cf.py](exact_cf.py), [typed_intervals.py](typed_intervals.py) | Exact continued fractions, algebraic arithmetic, and interval types |
| [obstruction_probe.py](obstruction_probe.py) | Forbidden-word automaton and extremal tails |
| [box_certificates.py](box_certificates.py), [anchor_boxes.py](anchor_boxes.py), [typed_boxes.py](typed_boxes.py) | Parameter boxes and uniform interval comparisons |
| [endpoint_certificate.py](endpoint_certificate.py) | Verify successor menus and destinations |
| [spectral_bounds.py](spectral_bounds.py) | Bounds on noncentral local values |
| [width_catalog.py](width_catalog.py) | Normalized difference and width bounds; also retains a discovery CLI |
| [typed_catalog.py](typed_catalog.py), [typed_search.py](typed_search.py), [menu_search.py](menu_search.py), [adaptive_menus.py](adaptive_menus.py) | Helpers retained in the current input-generation/import chain, with earlier search APIs |
| [verify_hall_ray.py](verify_hall_ray.py) | `check_row` and interval-chain helpers used by current verifiers; its standalone CLI verifies the earlier whole-ray construction |
| [write_hall_tables.py](write_hall_tables.py) | Render the saved initial-cover tables for documentation |

[src/layout.py](../src/layout.py) is intentionally retained as the shared path
resolver so that existing manifests and source bytes remain valid.

Use root `run.py` for standalone execution at these new paths. Some discovery
helpers use NumPy; exact reverification uses the Python standard library.
