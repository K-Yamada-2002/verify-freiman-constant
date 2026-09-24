#!/usr/bin/env python3
"""Exact fixed-root transfer probe for the adjusted Schecker case lists.

This is a diagnostic, not an induction verifier.  It reads ORIGINAL_CASES
from the source notebook, applies the same direction/order conversion used
there, and checks those finite successor intervals against selected roots of
the 31313-free target family in Q(sqrt(462)).
"""
from __future__ import annotations

import ast
import json
import sys
from fractions import Fraction as F
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
NOTEBOOK = ROOT / "Schecker" / "schecker_proof_2.ipynb"
OUTPUT = HERE / "schecker_template_transfer_20260925.json"
sys.path.insert(0, str(HERE))
import explore  # noqa: E402


def read_original_cases():
    notebook = json.loads(NOTEBOOK.read_text())
    cell = next(
        cell for cell in notebook["cells"]
        if cell.get("cell_type") == "code"
        and any("ORIGINAL_CASES = [" in line for line in cell["source"])
    )
    tree = ast.parse("".join(cell["source"]))
    assignment = next(
        node for node in tree.body
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name)
                and target.id == "ORIGINAL_CASES"
                for target in node.targets)
    )
    return ast.literal_eval(assignment.value)


def word(suffix):
    return "".join(map(str, suffix))


def adjusted_pairs(original_family, family_number):
    """Mirror notebook conversion: swap directions; reverse lists in 4–6."""
    result = []
    for case in original_family["cases"]:
        intervals = case["intervals"]
        if family_number in (4, 5, 6):
            intervals = list(reversed(intervals))
        result.append([(word(positive), word(negative))
                       for negative, positive in intervals])
    return result


def interval_gap_record(gap):
    return [endpoint.record() for endpoint in gap]


def uncovered_parts(target, intervals):
    """Return exact gaps in the union of intervals inside target."""
    lo, hi = target
    cursor = lo
    result = []
    for child_lo, child_hi in explore.merge(intervals):
        child_lo, child_hi = max(lo, child_lo), min(hi, child_hi)
        if child_hi <= child_lo:
            continue
        if cursor < child_lo:
            result.append((cursor, child_lo))
        if cursor < child_hi:
            cursor = child_hi
    if cursor < hi:
        result.append((cursor, hi))
    return result


def check_case(parent_left, parent_right, pairs):
    intervals = []
    children = []
    for left_suffix, right_suffix in pairs:
        left, right = parent_left + left_suffix, parent_right + right_suffix
        try:
            child_interval = explore.hull(left, right)
        except ValueError as error:
            children.append({
                "left_suffix": left_suffix,
                "right_suffix": right_suffix,
                "legal": False,
                "reason": str(error),
            })
            continue
        v_low = explore.full_ratio_compare(left, right, F(5, 17)) >= 0
        v_high = explore.full_ratio_compare(left, right, F(17, 5)) <= 0
        intervals.append(child_interval)
        children.append({
            "left_suffix": left_suffix,
            "right_suffix": right_suffix,
            "legal": True,
            "old_v_admissible_5_over_17_to_17_over_5": v_low and v_high,
            "old_v_display": explore.full_ratio_float(left, right),
            "interval": interval_gap_record(child_interval),
        })
    merged = explore.merge(intervals)
    return {
        "children": children,
        "child_interval_union": [interval_gap_record(i) for i in merged],
        "uncovered_parts_of_parent_hull": [],
        "legal_child_count": sum(row["legal"] for row in children),
        "old_v_admissible_child_count": sum(
            row.get("old_v_admissible_5_over_17_to_17_over_5", False)
            for row in children
        ),
    }, intervals


def old_v_admissible(left, right):
    return (
        explore.full_ratio_compare(left, right, F(5, 17)) >= 0
        and explore.full_ratio_compare(left, right, F(17, 5)) <= 0
    )


def greedy_cover_domain(left, right, domain, max_total):
    """Cover a carried interval by admissible descendant hulls, left to right."""
    candidates = []
    for total in range(1, max_total + 1):
        for left_count in range(total + 1):
            for child_left in explore.extensions(left, left_count):
                for child_right in explore.extensions(right, total - left_count):
                    if not old_v_admissible(child_left, child_right):
                        continue
                    lo, hi = explore.hull(child_left, child_right)
                    lo, hi = max(lo, domain[0]), min(hi, domain[1])
                    if lo < hi:
                        candidates.append((lo, hi, child_left, child_right, total))

    cursor = domain[0]
    used = set()
    selected = []
    while cursor < domain[1]:
        available = [
            row for row in candidates
            if row[0] <= cursor < row[1] and (row[2], row[3]) not in used
        ]
        if not available:
            return None, len(candidates)
        best = max(available, key=lambda row: row[1])
        used.add((best[2], best[3]))
        end = min(best[1], domain[1])
        selected.append((best[2], best[3], (cursor, end), best[4]))
        cursor = end
    return selected, len(candidates)


def target_carry_probe(left, right, target, max_level=4, max_total=3):
    """Record a bounded greedy run; failure is diagnostic, not a disproof."""
    root_cover, candidate_count = greedy_cover_domain(left, right, target, 2)
    if root_cover is None:
        root_data = {"covered": False, "candidate_count": candidate_count}
    else:
        root_data = {
            "covered": True,
            "candidate_count": candidate_count,
            "selected_children": [],
        }
        for child_left, child_right, assigned, added in root_cover:
            depth3_gaps = [
                (max(lo, assigned[0]), min(hi, assigned[1]))
                for lo, hi in explore.gaps(
                    explore.outer_components(child_left, child_right, 3)
                )
                if max(lo, assigned[0]) < min(hi, assigned[1])
            ]
            root_data["selected_children"].append({
                "left": child_left,
                "right": child_right,
                "added_total": added,
                "assigned_domain": interval_gap_record(assigned),
                "old_v_display": explore.full_ratio_float(child_left, child_right),
                "depth_3_outer_gaps_intersecting_assigned_domain": [
                    interval_gap_record(gap) for gap in depth3_gaps
                ],
            })

    frontier = [(left, right, target)]
    level_counts = []
    first_failure = None
    for level in range(max_level):
        next_frontier = []
        failures = []
        for node_left, node_right, domain in frontier:
            cover, count = greedy_cover_domain(
                node_left, node_right, domain, max_total
            )
            if cover is None:
                failures.append((node_left, node_right, domain, count))
            else:
                next_frontier.extend(
                    (child_left, child_right, child_domain)
                    for child_left, child_right, child_domain, _ in cover
                )
        level_counts.append({
            "level": level,
            "obligation_count": len(frontier),
            "failed_obligations": len(failures),
            "produced_children": len(next_frontier),
        })
        if failures:
            node_left, node_right, domain, count = failures[0]
            gaps = [
                (max(lo, domain[0]), min(hi, domain[1]))
                for lo, hi in explore.gaps(
                    explore.outer_components(node_left, node_right, 1)
                )
                if max(lo, domain[0]) < min(hi, domain[1])
            ]
            first_failure = {
                "left": node_left,
                "right": node_right,
                "assigned_domain": interval_gap_record(domain),
                "candidate_count_at_max_total": count,
                "depth_1_outer_gaps_intersecting_assigned_domain": [
                    interval_gap_record(gap) for gap in gaps
                ],
            }
            break
        frontier = next_frontier
    return {
        "meaning": (
            "Greedy hull-cover exploration only. A reported gap proves that this "
            "particular assigned child domain fails; it does not rule out a different "
            "overlapping parent cover."
        ),
        "root_cover_with_successors_of_total_length_at_most_2": root_data,
        "recursive_levels": level_counts,
        "first_greedy_failure": first_failure,
    }


def build_report(max_n=3):
    original_cases = read_original_cases()
    roots = []
    for n in range(max_n + 1):
        # The v>=1 orientation is (V_n, U_n); the sum interval is unchanged.
        u = "3211" + "313121" * n + "3"
        v = "4322" + "313121" * n
        left, right = v, u
        target = explore.hull(left, right)
        root_v_in_family = (
            explore.full_ratio_compare(left, right, F(1)) >= 0
            and explore.full_ratio_compare(left, right, F(19, 10)) <= 0
        )

        family_results = {}
        all_candidate_intervals = []
        for family_number in (4, 5):
            case_results = []
            family_intervals = []
            for pairs in adjusted_pairs(original_cases[family_number - 1], family_number):
                result, intervals = check_case(left, right, pairs)
                result["uncovered_parts_of_parent_hull"] = [
                    interval_gap_record(g)
                    for g in uncovered_parts(target, intervals)
                ]
                case_results.append(result)
                family_intervals.extend(intervals)
            family_results[str(family_number)] = {
                "case_count": len(case_results),
                "cases": case_results,
                "all_alternative_child_intervals": [
                    interval_gap_record(i) for i in explore.merge(family_intervals)
                ],
                "all_alternatives_uncovered_parts_of_parent_hull": [
                    interval_gap_record(g)
                    for g in uncovered_parts(target, family_intervals)
                ],
            }
            all_candidate_intervals.extend(family_intervals)

        combined = explore.merge(all_candidate_intervals)
        residuals = uncovered_parts(target, all_candidate_intervals)
        cap_left, cap_right = left + "13", right + "31"
        cap_interval = explore.hull(cap_left, cap_right)
        cap_cover = (
            greedy_cover_domain(cap_left, cap_right,
                                (residuals[0][0], residuals[-1][1]), 2)
            if residuals else ([], 0)
        )
        cap_descendants = []
        if cap_cover[0] is not None:
            for child_left, child_right, assigned, added in cap_cover[0]:
                depth3_gaps = [
                    (max(lo, assigned[0]), min(hi, assigned[1]))
                    for lo, hi in explore.gaps(
                        explore.outer_components(child_left, child_right, 3)
                    )
                    if max(lo, assigned[0]) < min(hi, assigned[1])
                ]
                cap_descendants.append({
                    "left": child_left,
                    "right": child_right,
                    "added_total": added,
                    "assigned_domain": interval_gap_record(assigned),
                    "old_v_display": explore.full_ratio_float(child_left, child_right),
                    "depth_3_outer_gaps_intersecting_assigned_domain": [
                        interval_gap_record(gap) for gap in depth3_gaps
                    ],
                })
        cap_data = {
            "suffixes": ["13", "31"],
            "legal": True,
            "old_v_admissible_5_over_17_to_17_over_5": old_v_admissible(
                cap_left, cap_right
            ),
            "interval": interval_gap_record(cap_interval),
            "covers_every_template_residual": bool(residuals) and all(
                cap_interval[0] <= lo and hi <= cap_interval[1]
                for lo, hi in residuals
            ),
            "carried_residual_cover_with_descendant_total_at_most_2": {
                "covered": cap_cover[0] is not None,
                "candidate_count": cap_cover[1],
                "selected_children": cap_descendants,
            },
        }
        # One short, ordered chain selected from the Schecker case families,
        # plus the target-specific cap. The n=0 and n>=1 chains differ once.
        chain_suffixes = (
            [("", "1"), ("1", "2"), ("11", "3"), ("12", "3"), ("13", "31")]
            if n == 0 else
            [("", "1"), ("3", "3"), ("1", "2"),
             ("11", "3"), ("12", "3"), ("13", "31")]
        )
        chain_intervals = []
        chain_items = []
        for left_suffix, right_suffix in chain_suffixes:
            child_left, child_right = left + left_suffix, right + right_suffix
            child_interval = explore.hull(child_left, child_right)
            chain_intervals.append(child_interval)
            chain_items.append({
                "left_suffix": left_suffix,
                "right_suffix": right_suffix,
                "old_v_admissible_5_over_17_to_17_over_5": old_v_admissible(
                    child_left, child_right
                ),
                "interval": interval_gap_record(child_interval),
            })
        chain_union = explore.merge(chain_intervals)
        refined_chain = []
        for depth in range(5):
            refined_intervals = []
            for left_suffix, right_suffix in chain_suffixes:
                child_left, child_right = left + left_suffix, right + right_suffix
                if depth == 0:
                    refined_intervals.append(explore.hull(child_left, child_right))
                else:
                    refined_intervals.extend(
                        explore.outer_components(child_left, child_right, depth)
                    )
            refined_union = explore.merge(refined_intervals)
            refined_gaps = uncovered_parts(target, refined_intervals)
            refined_chain.append({
                "depth_below_selected_successors": depth,
                "component_count": len(refined_union),
                "uncovered_parts_of_parent_hull": [
                    interval_gap_record(gap) for gap in refined_gaps
                ],
                "covers_parent_hull": not refined_gaps,
            })
        roots.append({
            "n": n,
            "U_n": u,
            "V_n": v,
            "normalized_left": left,
            "normalized_right": right,
            "old_v_display": explore.full_ratio_float(left, right),
            "old_v_in_both_family_ranges_1_to_1_9": root_v_in_family,
            "target_convex_hull_without_central_4": interval_gap_record(target),
            "families": family_results,
            "union_of_every_candidate_from_families_4_and_5": [
                interval_gap_record(i) for i in combined
            ],
            "combined_uncovered_parts_of_parent_hull": [
                interval_gap_record(g)
                for g in uncovered_parts(target, all_candidate_intervals)
            ],
            "combined_cover": not uncovered_parts(target, all_candidate_intervals),
            "endpoint_cap": cap_data,
            "short_document_chain_plus_cap": {
                "selected_successors": chain_items,
                "selected_child_interval_union": [
                    interval_gap_record(i) for i in chain_union
                ],
                "covers_parent_hull": not uncovered_parts(target, chain_intervals),
                "refined_outer_cover": refined_chain,
            },
        })
    first_root = roots[0]
    first_target = explore.hull(
        first_root["normalized_left"], first_root["normalized_right"]
    )
    return {
        "scope": (
            "Exact fixed-root transfer probe only; it does not prove a uniform "
            "parameter-family cover or induction closure."
        ),
        "arithmetic": "Exact Q(sqrt(462)) intervals and exact Q(sqrt(21)) old-v comparisons",
        "source_case_data": str(NOTEBOOK.relative_to(ROOT)),
        "conversion": (
            "Same as notebook case_families: swap each successor direction; "
            "also reverse case interval order in families 4–6."
        ),
        "children_checked_against_old_v_range": ["5/17", "17/5"],
        "roots": roots,
        "target_value_carried_probe_at_n_0": target_carry_probe(
            first_root["normalized_left"], first_root["normalized_right"],
            first_target,
        ),
    }


if __name__ == "__main__":
    report = build_report()
    OUTPUT.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"wrote {OUTPUT}")
    for row in report["roots"]:
        print(
            f"n={row['n']} v={row['old_v_display']} "
            f"family_ranges={row['old_v_in_both_family_ranges_1_to_1_9']} "
            f"combined_cover={row['combined_cover']} "
            f"residual_gaps={len(row['combined_uncovered_parts_of_parent_hull'])}"
        )
