#!/usr/bin/env python3
"""Propose the finite-ray witnesses; every bound and endpoint is rechecked in Lean."""
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
sys.path.insert(0, str(REPO / "Freiman"))
from prepare import K, interval, scan


def export():
    source = REPO / "Freiman/certificates/ray.json"
    data = json.loads(source.read_text())
    meta = json.loads((source.parent / "graph_wide.meta.json").read_text())
    candidates = []
    for row in data["finite_chain"]:
        children = data["initial_entrances"][row["entrance"]]["menu"] if "entrance" in row else [row]
        theta = K(*row["theta_upper"]) + K(Q(1, 10**8))
        for child in children:
            a, b = (tuple(map(int, child[key])) for key in ("a", "b"))
            lo, hi = interval(a, b)
            for proof in child["proofs"]:
                p, q = map(Q, proof["band"])
                rawlo, rawhi = lo+p*(hi-lo), lo+q*(hi-lo)
                lower, upper = max(rawlo+row["center"], theta), rawhi+row["center"]
                if lower < upper:
                    ia, ib = divmod(proof["geometry"], len(meta["side_keys"]))
                    witness = (child["a"], child["b"], ia, ib,
                               proof["bin"]-meta["low"], proof["type"])
                    spectral = (child["a"], child["b"], row["center"], theta)
                    candidates.append((lower, upper, witness, rawlo, rawhi, spectral))
    candidates.sort(key=lambda r: r[0])
    start = K(*data["endpoint_interval"][1])
    current = start
    chain = []
    index = 0
    while current < K(Q(13, 2)):
        chosen = None
        while index < len(candidates) and candidates[index][0] <= current:
            candidate = candidates[index]
            if chosen is None or chosen[1] < candidate[1]:
                chosen = candidate
            index += 1
        if chosen is None or chosen[1] <= current:
            raise ValueError(f"Finite-chain gap at {current.data()}")
        chain.append(chosen)
        current = chosen[1]
    spectra = []
    spectrum_ids = {}
    for row in chain:
        a,b,c,t = row[-1]
        key = a,b,c,t.a,t.b
        if key not in spectrum_ids:
            spectrum_ids[key] = len(spectra)
            spectra.append(row[-1])
    tokens = [str(len(spectra))]
    def word(w):
        tokens.extend([str(len(w)), *w])
    def quad(q):
        for c in q.data():
            v = Q(c)
            tokens.extend([str(v.numerator), str(v.denominator)])
    for a,b,c,theta in spectra:
        word(a); word(b)
        tokens.extend([str(c), str(len(scan(tuple(map(int,a))))), str(len(scan(tuple(map(int,b)))))])
        quad(theta)
    quad(start)
    quad(K(Q(13,2)))
    tokens.append(str(len(chain)))
    for lo,hi,(a,b,ia,ib,bin_,typ),rawlo,rawhi,(sa,sb,c,theta) in chain:
        word(a); word(b)
        tokens.extend(map(str,(ia,ib,bin_,typ)))
        quad(rawlo); quad(rawhi)
        tokens.append(str(spectrum_ids[(sa,sb,c,theta.a,theta.b)]))
        quad(lo); quad(hi)
    path = HERE / "generated/freiman_finite.txt"
    path.parent.mkdir(exist_ok=True)
    path.write_text(" ".join(tokens)+"\n")
    manifest = {"spectral_roots":len(spectra),"finite_rows":len(chain),
                "finite_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                "ray_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
                "lower":start.data(),"upper":["13/2","0"],
                "spectral_slack":"1/100000000"}
    (path.parent / "freiman_finite_manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    return manifest


if __name__ == "__main__":
    print(json.dumps(export(),indent=2))
