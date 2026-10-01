#!/usr/bin/env python3
"""Run every geometry through the compiled, proved-sound Lean checker.

The witness exporter is untrusted. This is execution evidence, not a kernel
proof of the large Boolean acceptance proposition.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[1]
GENERATED = HERE / "generated"
INPUT = REPO / "Freiman/data/graph_wide.dat"
ALIVE = REPO / "Freiman/data/graph_wide.json.alive.bin"
EXE = HERE / ".lake/build/bin/graphReplay"
WITNESSES = GENERATED / "witnesses"
RANGES = [(0, 121), (121, 242), (242, 363), (363, 484)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def provenance():
    files = {f"geometry_{g}.bin": sha(WITNESSES / f"geometry_{g}.bin") for g in range(484)}
    return {
        "input_sha256": sha(INPUT), "alive_sha256": sha(ALIVE),
        "executable_sha256": sha(EXE),
        "witness_files": files,
        "witness_manifest_sha256": hashlib.sha256(
            json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
    }


def summarize_shard(begin, end, log, error_log, exit_code):
    if exit_code != 0:
        raise RuntimeError(f"replay [{begin},{end}) failed; see {error_log}")
    if error_log.read_text().strip():
        raise RuntimeError(f"unexpected replay stderr: {error_log}")
    output = log.read_text()
    rows = re.findall(r"^geometry=(\d+) rows=(\d+) cells=(\d+) selected_vertices=(\d+) "
                      r"path_nodes=(\d+) elapsed_ms=(\d+)$", output, re.M)
    if [int(row[0]) for row in rows] != list(range(begin, end)):
        raise RuntimeError(f"missing, duplicate or unordered geometry: {log}")
    summaries = re.findall(r"^accepted geometries=\[(\d+),(\d+)\) adopted_rows=(\d+) adopted_cells=(\d+)$",
                           output, re.M)
    if len(summaries) != 1:
        raise RuntimeError(f"missing unique acceptance summary: {log}")
    a, b, nrows, ncells = map(int, summaries[0])
    last = list(map(int, rows[-1]))
    if (a, b, nrows, ncells) != (begin, end, last[1], last[2]):
        raise RuntimeError(f"inconsistent replay totals: {log}")
    return {"begin": begin, "end": end, "exit_code": exit_code,
            "log": str(log.relative_to(HERE)), "log_sha256": sha(log),
            "stderr_log": str(error_log.relative_to(HERE)),
            "rows": nrows, "cells": ncells, "selected_vertices": last[3],
            "path_nodes": last[4], "elapsed_ms": last[5]}


def replay_shard(bounds):
    begin, end = bounds
    log = GENERATED / f"replay_{begin}_{end}.log"
    err = GENERATED / f"replay_{begin}_{end}.errors.log"
    with log.open("w") as stdout, err.open("w") as stderr:
        completed = subprocess.run([str(EXE), str(INPUT), str(ALIVE), str(WITNESSES),
                                    str(begin), str(end)], cwd=HERE, stdout=stdout, stderr=stderr)
    result = summarize_shard(begin, end, log, err, completed.returncode)
    print(f"Accepted [{begin},{end}): {result['rows']} rows", flush=True)
    return result


def total_report(shards, hashes):
    if [(s["begin"], s["end"]) for s in shards] != RANGES:
        raise RuntimeError("shard ranges do not partition all 484 geometries")
    totals = {key: sum(s[key] for s in shards)
              for key in ("rows", "cells", "selected_vertices", "path_nodes")}
    if totals["rows"] != 3464816 or totals["cells"] != 150040:
        raise RuntimeError(f"unexpected immutable table totals: {totals}")
    return {"accepted": True, "acceptance_method": "compiled Lean checker execution",
            "kernel_reduction_of_large_table": False,
            "semantic_and_root_checks_in_each_shard": True,
            "geometries": 484, **totals, **hashes, "shards": shards}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true", help="build and run the untrusted witness exporter")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error("jobs must be 1..4")
    GENERATED.mkdir(exist_ok=True)
    destination = GENERATED / "replay_report.json"
    destination.unlink(missing_ok=True)
    if args.prepare:
        exporter = GENERATED / "export_graph"
        subprocess.run(["c++", "-std=c++17", "-O3", str(HERE / "scripts/export_graph.cpp"),
                        "-o", str(exporter)], check=True, cwd=HERE)
        subprocess.run([str(exporter), str(INPUT), str(ALIVE), str(WITNESSES)], check=True, cwd=HERE)
    before = provenance()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        shards = list(pool.map(replay_shard, RANGES))
    if provenance() != before:
        raise RuntimeError("executable, input, bitmap or witnesses changed during replay")
    report = total_report(shards, before)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "witness_files"}, indent=2))


if __name__ == "__main__":
    main()
