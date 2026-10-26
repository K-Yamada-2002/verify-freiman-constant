# Discovery and input generation

| Source | Role |
|---|---|
| [kernel_input.py](kernel_input.py) | Select finite states, interval types, and successor candidates; generate numerical discovery data and metadata |
| [certified_kernel_input.py](certified_kernel_input.py) | Regenerate rigorous integer-interval input from metadata |
| [graph_kernel_expand.cpp](graph_kernel_expand.cpp) | Expand the finite table from a protected seed |
| [endpoint_return.py](endpoint_return.py) | Shared closed-table access and endpoint successor search |
| [adaptive_return_chart.py](adaptive_return_chart.py) | Discover deeper successor covers for the endpoint conditions |
| [wide_bootstrap_search.py](wide_bootstrap_search.py) | Discover entrances into `graph_wide` |
| [make_unified_certificate.py](make_unified_certificate.py) | Assemble the current fixed whole-proof certificate; verification is separate |
| [root_search.py](root_search.py), [refine_roots.py](refine_roots.py), [augment_roots.py](augment_roots.py), [bridge_search.py](bridge_search.py), [build_hall_certificate.py](build_hall_certificate.py) | Root/bridge discovery and assembly stages underlying the saved initial-cover construction |

The ordinary deletion search is implemented in
**[../verify/graph_kernel.cpp](../verify/graph_kernel.cpp)**. Passing only input
and output paths starts a search; supplying an adoption file requests fixed-table
verification. The expansion search requires later verification without seed
protection.

`kernel_input.py`'s numerical `.dat` is not the rigorous graph input. Its metadata
is read by `certified_kernel_input.py --graph` to generate the latter. Exact
regeneration of the saved wide input can be run without overwriting it:

```sh
python3 -B -S -m Freiman.search.certified_kernel_input graph_wide --name /tmp/graph_wide_input --graph --tight
```

Run Python sources from the repository root with `python3 -m Freiman.<directory>.<module>`.
See the [code guide](../../README.md#code-start-here) for actual search/replay commands.
