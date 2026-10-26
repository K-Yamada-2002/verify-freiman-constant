# Retained research and earlier constructions

These files preserve earlier proofs, alternative kernels, compression searches,
and bounded experiments. Start with [verify/](../verify/README.md) and
[search/](../search/README.md) for the current proof and adopted table.

In particular:

- `graph_kernel_queue.cpp` is the earlier queue-based cross-check;
  `graph_kernel_reduce.cpp` and `simple_family_grouped_reduce.cpp` support
  restricted-family searches.
- `search_small_family.py`, `prepare_coarse_search.py`, `simple_family_m1.py`,
  `compress_admissibility.py`, and `admissibility_rectangle_bound.py` concern
  compression or different representations.
- `verify_endpoint_closure.py`, `verify_typed.py`, `verify_width_rows.py`,
  `wide_bootstrap_verify.py`, and `audit_schecker_proof.py` retain earlier or
  component-level verification routes. These are not all failed experiments.
- `periodic_exception.py` and the other discovery variants document research
  history; a bounded failure is not a nonexistence theorem.

No historical result has been deleted or reclassified as a proof. Saved data
and logs remain under `data/` and `logs/`. Old `src/` links preserve references
in the existing detailed documents. To execute a moved script, use root
`run.py`, for example:

```sh
python3 -B -S run.py Freiman/history/admissibility_rectangle_bound.py
```
