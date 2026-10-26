# Shared arithmetic and bounds

| Sources | Responsibility |
|---|---|
| [field.py](field.py) | Exact algebraic arithmetic |
| [exact_cf.py](exact_cf.py), [language.py](language.py) | Continued fractions and forbidden-word states |
| [spectral_rational.py](spectral_rational.py) | Separate rational outer bounds for noncentral values |
| [compatible_past.py](compatible_past.py), [tail_replacement.py](tail_replacement.py) | Compatible-past replacement and all-position bounds |
| [prepare.py](prepare.py) | `enclosing`, used by the current exact input generator; its standalone CLI concerns the earlier `131` problem |

These are dependencies of [verify/](../verify/README.md) and
[search/](../search/README.md), not additional proof entry points.
The separately implemented checks remain in [audit/](../audit/).
Use the snapshot’s flat `src/` paths if executing a source at its new path.
