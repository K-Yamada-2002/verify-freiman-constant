#!/usr/bin/env python3
"""Build the mathematical soundness theorem and replay its finite certificate.

The large-table acceptance is checked by compiled Lean execution, not imported
as an axiom or claimed to be a kernel-reduced closed theorem.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import replay

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[1]
LOGS = HERE / "logs"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run_logged(command, name):
    print("Running:", " ".join(command), flush=True)
    result = subprocess.run(command, cwd=HERE, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (LOGS / name).write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def check_provenance():
    sources = json.loads((HERE / "sources.json").read_text())
    groups = [(REPO, sources["source_sha256"]), (HERE, sources["vendored_source"]["files"])]
    count = 0
    for base, records in groups:
        for name, expected in records.items():
            if replay.sha(base / name) != expected:
                raise SystemExit(f"Provenance mismatch: {name}")
            count += 1
    return count


def audit_axioms(output):
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", output)
    expected = re.findall(r"^#print axioms (\S+)", (HERE / "Audit.lean").read_text(), re.M)
    checked = {name for name, _ in records} | set(no_axioms)
    if checked != set(expected):
        raise SystemExit(f"Incomplete axiom output: expected {expected}, got {sorted(checked)}")
    result = {name: [] for name in no_axioms}
    for name, names in records:
        used = {v.strip() for v in names.split(",") if v.strip()}
        allowed = STANDARD_AXIOMS
        if not used <= allowed:
            raise SystemExit(f"Unexpected logical dependency in {name}: {used - allowed}")
        result[name] = sorted(used)
    return result


def checked_replay_report():
    report = json.loads((HERE / "generated/replay_report.json").read_text())
    hashes = replay.provenance()
    for key, value in hashes.items():
        if report.get(key) != value:
            raise SystemExit(f"Replay assets changed: {key}; run without --reuse-replay")
    shards = []
    for shard in report["shards"]:
        log, err = HERE / shard["log"], HERE / shard["stderr_log"]
        if replay.sha(log) != shard["log_sha256"]:
            raise SystemExit(f"Replay log changed: {log}")
        shards.append(replay.summarize_shard(shard["begin"], shard["end"], log, err, shard["exit_code"]))
    reconstructed = replay.total_report(shards, hashes)
    if report != reconstructed:
        raise SystemExit("Replay report does not match its logs and current assets")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-replay", action="store_true",
                        help="reuse successful full replay only after matching all asset/log hashes")
    parser.add_argument("--prepare", action="store_true", help="regenerate untrusted witness files")
    args = parser.parse_args()
    if args.prepare and args.reuse_replay:
        parser.error("--prepare and --reuse-replay cannot be combined")
    LOGS.mkdir(exist_ok=True)
    report_path = LOGS / "verification.json"
    report_path.unlink(missing_ok=True)
    source_count = check_provenance()
    compiler_version = run_logged(["lake", "env", "lean", "--version"], "toolchain.log").strip()
    run_logged(["lake", "build", "Berstein", "graphReplay"], "build.log")
    axioms = audit_axioms(run_logged(["lake", "env", "lean", "Audit.lean"], "axioms.log"))
    if not args.reuse_replay:
        command = [sys.executable, "scripts/replay.py"]
        if args.prepare:
            command.append("--prepare")
        run_logged(command, "replay.log")
    accepted = checked_replay_report()
    negative_output = run_logged(["lake", "env", "lean", "Berstein/NegativeControls.lean"],
                                 "negative-controls.log")
    negative = re.findall(r"^PASS rejected corruption: (.+)$", negative_output, re.M)
    if len(negative) != 6 or len(set(negative)) != 6 or "PASS accepted baseline" not in negative_output:
        raise SystemExit("Incomplete negative-control output")
    lean_sources = {str(p.relative_to(HERE)): replay.sha(p)
                    for p in sorted(HERE.rglob("*.lean"))
                    if not any(part in {".lake", "generated"} for part in p.relative_to(HERE).parts)}
    report = {
        "verified_at": datetime.now(timezone.utc).isoformat(),
        "compiler_version": compiler_version,
        "result_verified_via_sound_checker": True,
        "checker_to_markov_spectrum_soundness_proved": True,
        "analytic_obligations_remaining": [],
        "large_table_acceptance_method": "compiled Lean checker; all adopted rows",
        "large_table_acceptance_kernel_reduced": False,
        "closed_kernel_theorem_for_concrete_large_table": False,
        "claimed_interval": ["226289/50000", "226377/50000"],
        "excluded_ray": "[freimanConstant, infinity)",
        "axiom_audit": axioms,
        "negative_controls": negative,
        "provenance_files_checked": source_count,
        "toolchain": (HERE / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": replay.sha(HERE / "lake-manifest.json"),
        "lean_source_sha256": lean_sources,
        "support_source_sha256": {str(p.relative_to(HERE)): replay.sha(p)
                                  for p in sorted((HERE / "scripts").glob("*"))
                                  if p.is_file() and p.suffix in {".py", ".cpp"}},
        "execution_trust": ["Lean compiler and runtime", "IO/parser", "host arithmetic/runtime execution"],
        "untrusted_proposers": ["scripts/export_graph.cpp", "scripts/export_semantics.py"],
        "replay": accepted,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified interval via proved-sound checker; {accepted['rows']} rows, "
          f"{len(negative)} rejected corruptions. Report: {report_path}")


if __name__ == "__main__":
    main()
