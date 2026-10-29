#!/usr/bin/env python3
"""Verify checker soundness and concrete acceptance for [c_F,infinity) in M.

The mathematical implication is kernel checked. Large-table and finite data
acceptance are established by executing the proved-sound Lean checkers.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
LOGS = HERE / "logs"
GENERATED = HERE / "generated"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, name):
    print("Running " + " ".join(map(str, command)), flush=True)
    log = LOGS / name
    with log.open("w") as output:
        result = subprocess.run(command, cwd=HERE, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Verification failed; see {log}")
    return log.read_text()


def source_hashes():
    paths = [p for p in HERE.rglob("*.lean")
             if not any(part in {".lake", "generated", "logs"}
                        for part in p.relative_to(HERE).parts)]
    paths += [p for p in (HERE / "scripts").iterdir() if p.suffix in {".py", ".cpp"}]
    paths += [HERE / "Freiman.lean", HERE / "SpectrumVerification.lean",
              HERE / "lakefile.toml", HERE / "lake-manifest.json", HERE / "lean-toolchain", HERE / "sources.json",
              HERE / "scripts/verify.py", HERE / "scripts/replay.py",
              REPO / "Freiman/prepare.py", REPO / "Freiman/proof.py"]
    paths += list((REPO / "Freiman/certificates").glob("*"))
    return {str(p.relative_to(REPO)): sha(p) for p in sorted(set(paths)) if p.is_file()}


def generated_hashes():
    return {p.name: sha(p) for p in sorted(GENERATED.glob("freiman_*")) if p.is_file()}


def read_manifests():
    result = {}
    ray_sha = sha(REPO / "Freiman/certificates/ray.json")
    for key in ("roots", "finite", "local"):
        result[key] = json.loads((GENERATED / f"freiman_{key}_manifest.json").read_text())
        if result[key]["ray_sha256"] != ray_sha:
            raise SystemExit(f"Wrong ray source in {key} manifest")
    checks = {
        "freiman_roots.txt": result["roots"]["roots_sha256"],
        "freiman_upper.txt": result["roots"]["upper_cover_sha256"],
        "freiman_finite.txt": result["finite"]["finite_sha256"],
        "freiman_local.txt": result["local"]["local_sha256"],
    }
    for name, expected in checks.items():
        if sha(GENERATED / name) != expected:
            raise SystemExit(f"Generated file changed: {name}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-replay", action="store_true")
    args = parser.parse_args()
    LOGS.mkdir(exist_ok=True)
    report_file = LOGS / "freiman-verification.json"
    report_file.unlink(missing_ok=True)
    hashes = source_hashes()
    base_command = [sys.executable, "-B", "scripts/verify.py"]
    if args.reuse_replay:
        base_command.append("--reuse-replay")
    run(base_command, "freiman-table-verification.log")
    run(["lake", "build", "SpectrumVerification", "Freiman.ReplaySupport", "Freiman.LocalParser"], "freiman-build.log")
    for key in ("roots", "finite", "local"):
        run([sys.executable, "-B", f"scripts/export_freiman_{key}.py"], f"freiman-export-{key}.log")
    manifests = read_manifests()
    generated = generated_hashes()
    axioms_text = run(["lake", "env", "lean", "Freiman/Audit.lean"], "freiman-axioms.log")
    expected = re.findall(r"^#print axioms (\S+)", (HERE / "Freiman/Audit.lean").read_text(), re.M)
    found = dict((name, [a.strip() for a in values.split(",") if a.strip()])
                 for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axioms_text))
    found.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", axioms_text)})
    if set(found) != set(expected) or "Freiman.ray_subset_markov_of_check" not in found:
        raise SystemExit("Incomplete Freiman axiom audit")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if any(set(values) - allowed for values in found.values()):
        raise SystemExit("Unexpected axiom in Freiman proofs")
    summaries = {}
    for key, module in (("roots", "RootReplay"), ("finite", "FiniteReplay"), ("local", "LocalReplay")):
        output = run(["lake", "env", "lean", f"Freiman/{module}.lean"], f"freiman-{key}.log")
        lines = re.findall(r"^accepted .+$", output, re.M)
        if len(lines) != 1:
            raise SystemExit(f"Missing unique acceptance summary: {key}")
        summaries[key] = lines[0]
    expected_summaries = {
        "roots": f"accepted arbitrary_roots={manifests['roots']['root_count']} upper_cover_rows={manifests['roots']['upper_cover_rows']} negative_controls=7 whole_freiman_ray=false",
        "finite": f"accepted spectral_roots={manifests['finite']['spectral_roots']} finite_rows={manifests['finite']['finite_rows']} negative_controls=3",
        "local": f"accepted local_conditions={manifests['local']['conditions']} local_vertices={sum(manifests['local']['local_vertices'])} initial_interval=true negative_controls=8",
    }
    if summaries != expected_summaries:
        raise SystemExit(f"Unexpected acceptance summaries: {summaries}")
    read_manifests()
    if generated_hashes() != generated or source_hashes() != hashes:
        raise SystemExit("Sources, immutable certificates or generated data changed during verification")
    log_names = {"freiman-table-verification.log", "freiman-build.log", "freiman-axioms.log",
                 "freiman-roots.log", "freiman-finite.log", "freiman-local.log"}
    log_names.update(f"freiman-export-{key}.log" for key in ("roots", "finite", "local"))
    report = {
        "passed": True,
        "verified_at": datetime.now(timezone.utc).isoformat(),
        "toolchain": (HERE / "lean-toolchain").read_text().strip(),
        "complete_freiman_ray": True,
        "claim": "[c_F,infinity) is contained in the Markov spectrum",
        "theorem": "Freiman.ray_subset_markov_of_check",
        "scope_excludes": ["Lagrange-spectrum inclusion", "optimality below c_F"],
        "acceptance_method": "Lean checker execution; kernel-checked soundness implication",
        "kernel_reduction_of_large_table": False,
        "general_table_report_sha256": sha(LOGS / "verification.json"),
        "manifests": manifests,
        "acceptance_summaries": summaries,
        "negative_controls": {"general_table":6,"roots_and_upper_cover":7,"finite_ray":3,"local_and_initial":8},
        "axiom_audit": found,
        "source_sha256": hashes,
        "generated_sha256": generated,
        "log_sha256": {name: sha(LOGS / name) for name in sorted(log_names)},
    }
    report_file.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("passed", "complete_freiman_ray", "claim", "theorem")}, indent=2))


if __name__ == "__main__":
    main()
