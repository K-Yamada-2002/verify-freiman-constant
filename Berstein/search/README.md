# Table and root discovery

| Source | Role |
|---|---|
| [prepare_313.py](prepare_313.py) | Generate exact graph input for the selected forbidden words |
| [exploration_kernel.cpp](exploration_kernel.cpp) | Deletion search; distinguishes a closed family from unfinished bounded output |
| [search_313_intervals.py](search_313_intervals.py) | Discover root bands in the new closed table |
| [explore_intervals.py](explore_intervals.py), [refine_interval_gaps.py](refine_interval_gaps.py) | Discover/refine root intervals using the original `31313` table |
| [search_freiman_bridge.py](search_freiman_bridge.py) | Original below-ray root discovery |

The adopted new family is `avoid_alt5_spine10`, forbidding `31313,13131`.
Compile the search directly:

```sh
c++ -O3 -std=c++17 -pthread Berstein/search/exploration_kernel.cpp -o /tmp/berstein_search
```

Compile [../verify/graph_kernel.cpp](../verify/graph_kernel.cpp) for fixed-table
replay. Search and replay have separate entry points here. Run Python sources
through root `run.py` or the old `src/` compatibility paths. Detailed discovery
parameters, input audits and replay commands are in
[INTERVAL_EXPLORATION.md](../doc/INTERVAL_EXPLORATION.md).

A round limit with rows still remaining is an unfinished search, not a verified
closed table and not an empty-family result.
