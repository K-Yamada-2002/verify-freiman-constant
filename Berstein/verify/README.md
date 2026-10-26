# Verification

Start with **[graph_kernel.cpp](graph_kernel.cpp)** for fixed-table replay of
the extended `31313,13131` family. A separate implementation is in
[audit/independent_kernel.cpp](../audit/independent_kernel.cpp).

| Source | Role |
|---|---|
| [verify_below_ray.py](verify_below_ray.py) | Original interval, reusing Freiman's `31313` table |
| [verify_interval_extensions.py](verify_interval_extensions.py) | Extended roots and noncentral bounds for the original table |
| [verify_lower_intervals.py](verify_lower_intervals.py) | Fixed roots for the new `31313,13131` table; checks saved full replay records |
| [verify_exploration_bulk.py](verify_exploration_bulk.py) | Exact bulk bounds; this alone does not prove interval filling |
| [collect_exploration_results.py](collect_exploration_results.py) | Validate hashes and collect the completed results |

Run from the repository root:

```sh
python3 -B -S run.py Berstein/verify/verify_interval_extensions.py --full
python3 -B -S run.py Berstein/verify/verify_lower_intervals.py
python3 -B -S run.py Berstein/verify/collect_exploration_results.py
```

`verify_lower_intervals.py` does not rerun the C++ full-table checks; see the
[exploration report](../doc/INTERVAL_EXPLORATION.md#再現) for those commands.
Its old `src/` references remain valid. The [Lean development](../Lean/README.md)+covers the original table and interval, not the new table or extended endpoints.
