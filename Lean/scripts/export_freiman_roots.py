#!/usr/bin/env python3
"""Export untrusted arbitrary-word roots of the existing Freiman certificate.

The Lean root checker independently recomputes word states, parities, shapes,
scale ratios and table membership. This exporter does not certify local menus,
noncentral bounds or half-line inclusion.
"""
from pathlib import Path
import hashlib
import json
import sys
from fractions import Fraction as Q

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent


def export():
    source = REPO / "Freiman/certificates/ray.json"
    meta = json.loads((source.parent / "graph_wide.meta.json").read_text())
    data = json.loads(source.read_text())
    roots = set()
    translation_roots = set()

    def add(row, destination=roots):
        for proof in row.get("proofs", []):
            assert proof["kernel"] == "graph_wide"
            left, right = divmod(proof["geometry"], len(meta["side_keys"]))
            destination.add((row["a"], row["b"], left, right,
                       proof["bin"] - meta["low"], proof["type"]))

    for key in ("finite_chain", "translation_chain"):
        for row in data[key]:
            add(row)
    for row in data["initial_entrances"]:
        for child in row["menu"]:
            add(child)
    for row in data["translation_chain"]:
        if "entrance" in row:
            for child in data["initial_entrances"][row["entrance"]]["menu"]:
                add(child, translation_roots)
        else:
            add(row, translation_roots)
    assert roots
    words = [str(len(roots))]
    for a, b, left, right, bin_, type_ in sorted(roots):
        assert a and b and all(d in "1234" for d in a + b)
        words.extend([str(len(a)), *a, str(len(b)), *b,
                      str(left), str(right), str(bin_), str(type_)])
    destination = HERE / "generated/freiman_roots.txt"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(" ".join(words) + "\n")
    sys.path.insert(0, str(REPO / "Freiman"))
    from prepare import K, interval
    intervals = []
    for row in sorted(translation_roots):
        a, b = (tuple(map(int, w)) for w in row[:2])
        low, high = interval(a, b)
        p, q = map(Q, meta["bands"][row[-1]])
        intervals.append((low + p*(high-low), low + q*(high-low), row))
    intervals.sort(key=lambda r: r[0])
    current = K(Q(1, 2))
    chain = []
    index = 0
    while current < K(Q(3, 2)):
        chosen = None
        while index < len(intervals) and intervals[index][0] <= current:
            candidate = intervals[index]
            if chosen is None or chosen[1] < candidate[1]:
                chosen = candidate
            index += 1
        if chosen is None or chosen[1] <= current:
            raise ValueError("Translation roots do not cover the target")
        chain.append(chosen)
        current = chosen[1]
    def fraction_tokens(q):
        q = Q(q)
        return [str(q.numerator), str(q.denominator)]
    cover_words = [str(len(chain))]
    for low, high, (a, b, left, right, bin_, type_) in chain:
        cover_words.extend([str(len(a)), *a, str(len(b)), *b,
                            str(left), str(right), str(bin_), str(type_)])
        for endpoint in (low, high):
            for coefficient in endpoint.data():
                cover_words.extend(fraction_tokens(coefficient))
    cover_destination = HERE / "generated/freiman_upper.txt"
    cover_destination.write_text(" ".join(cover_words) + "\n")
    manifest = {
        "root_count": len(roots),
        "upper_cover_rows": len(chain),
        "upper_cover_sha256": hashlib.sha256(cover_destination.read_bytes()).hexdigest(),
        "word_pairs": len({r[:2] for r in roots}),
        "ray_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "roots_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
        "scope": "Arbitrary-word general-table roots only; not Freiman-ray verification",
    }
    (HERE / "generated/freiman_roots_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


if __name__ == "__main__":
    print(json.dumps(export(), indent=2))
