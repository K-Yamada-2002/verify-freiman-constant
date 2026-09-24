#!/usr/bin/env python3
"""Finite exact depth probe of old-v-admissible target descendants.

At each edge, append 1 or 2 legal digits in total and retain the child only
when its exact old Schecker ratio lies in [5/17, 17/5]. This measures whether
the union of surviving descendant hulls continues to cover the root interval.
Finite depth success is diagnostic and is not induction closure.
"""
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / "schecker_admissible_survivors_20260925.json"
sys.path.insert(0, str(HERE))
import explore  # noqa: E402


def admissible(left, right):
    return (
        explore.full_ratio_compare(left, right, F(5, 17)) >= 0
        and explore.full_ratio_compare(left, right, F(17, 5)) <= 0
    )


def gap_records(target, intervals):
    merged = explore.merge(intervals)
    cursor = target[0]
    gaps = []
    for lo, hi in merged:
        if cursor < lo:
            gaps.append((cursor, lo))
        if cursor < hi:
            cursor = hi
    if cursor < target[1]:
        gaps.append((cursor, target[1]))
    return merged, gaps


def run_root(n, depth_limit=5):
    u = "3211" + "313121" * n + "3"
    v = "4322" + "313121" * n
    left, right = v, u  # Orient the old v to be at least 1.
    target = explore.hull(left, right)
    frontier = {(left, right)}
    levels = []
    for depth in range(1, depth_limit + 1):
        following = set()
        for parent_left, parent_right in frontier:
            for total in (1, 2):
                for left_count in range(total + 1):
                    for child_left in explore.extensions(parent_left, left_count):
                        for child_right in explore.extensions(
                            parent_right, total - left_count
                        ):
                            if admissible(child_left, child_right):
                                following.add((child_left, child_right))
        intervals = [explore.hull(a, b) for a, b in following]
        components, gaps = gap_records(target, intervals)
        levels.append({
            "depth": depth,
            "surviving_prefix_pairs": len(following),
            "hull_union_component_count": len(components),
            "covers_entire_root_hull": not gaps,
            "uncovered_root_parts": [
                [lo.record(), hi.record()] for lo, hi in gaps
            ],
        })
        frontier = following
    return {
        "n": n,
        "U_n": u,
        "V_n": v,
        "normalized_old_v_display": explore.full_ratio_float(left, right),
        "root_hull_without_central_4": [x.record() for x in target],
        "edge_menu": "every legal extension pair adding 1 or 2 digits total",
        "edge_condition": "exact old v in [5/17,17/5]",
        "levels": levels,
    }


if __name__ == "__main__":
    report = {
        "scope": (
            "Exact finite-depth search only. It does not establish coverage at all "
            "depths or a finite induction closure."
        ),
        "arithmetic": "Exact Q(sqrt(462)) endpoints and exact Q(sqrt(21)) ratio tests",
        "roots": [run_root(0), run_root(1)],
    }
    OUTPUT.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"wrote {OUTPUT}")
    for root in report["roots"]:
        print(f"n={root['n']}")
        for row in root["levels"]:
            print(
                f"  depth={row['depth']} survivors={row['surviving_prefix_pairs']} "
                f"components={row['hull_union_component_count']} "
                f"covers={row['covers_entire_root_hull']}"
            )
