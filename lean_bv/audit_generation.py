#!/usr/bin/env python3
"""Host-side audit of the data embedded by generate_certificate.py.

This is not a substitute for Lean.  It catches transcription/generation
mistakes before a Lean-enabled machine performs proof-producing SAT replay.
"""

from __future__ import annotations

import hashlib
import itertools
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
PACKAGE_GRAPH = HERE.parent / "graph"
LEGACY_GRAPH = HERE.parent.parent / "Dirac_k4_order60_solution"
SOL = PACKAGE_GRAPH if PACKAGE_GRAPH.exists() else LEGACY_GRAPH
LEAN = HERE / "Dirac60" / "Certificate.lean"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    edges = [tuple(map(int, x.split())) for x in
             (SOL / "candidate60.edgelist").read_text().splitlines() if x]
    assert len(edges) == 180 and len(set(edges)) == 180
    assert all(0 <= u < v < 60 for u, v in edges)

    degree = [0] * 60
    for u, v in edges:
        degree[u] += 1
        degree[v] += 1
    assert degree == [6] * 60

    rows = []
    for deleted, line in enumerate(
        (SOL / "audits" / "vertex_witnesses.txt").read_text().splitlines()
    ):
        label, word = line.split()
        assert int(label) == deleted and len(word) == 60
        assert word[deleted] == "-"
        for u, v in edges:
            if deleted not in (u, v):
                assert word[u] != word[v]
        rows.append(word)
    assert len(rows) == 60

    log = (SOL / "audits" / "puncture_enumeration.O3.log").read_text()
    colourings = [m.group(1) for m in
                  re.finditer(r"^COLOURING \d+ ([-012]+)$", log, re.M)]
    assert len(colourings) == 16 and len(set(colourings)) == 16
    neighbours = [5, 26, 30, 33, 37, 55]
    expected_template = (
        "-0**21102120110012022002*1110202021202100*022201111120202021"
    )
    for word in colourings:
        assert len(word) == 60 and word[0] == "-"
        assert word[1] == "0" and word[6] == "1"
        assert sorted(word[v] for v in neighbours) == list("001122")
        for v, mark in enumerate(expected_template):
            if mark in "012":
                assert word[v] == mark
            elif mark == "*":
                allowed = "12" if v in (2, 41) else "01"
                assert word[v] in allowed
        for u, v in edges:
            if 0 not in (u, v):
                assert word[u] != word[v]

    observed = {(w[2], w[3], w[24], w[41]) for w in colourings}
    expected = set(itertools.product("12", "01", "01", "12"))
    assert observed == expected

    # Check the concrete q3=2 upper witness used in Lean.
    c = [1, 0, 1, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2,
         2, 0, 0, 2, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0,
         0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1]
    bad = [(u, v) for u, v in edges if c[u] == c[v]]
    assert bad == [(0, 5), (0, 26)]

    source = LEAN.read_text()
    assert "sorry" not in source and "admit" not in source
    assert len(re.findall(r"^  bv_decide$", source, re.M)) == 3
    assert len(re.findall(r"^  native_decide$", source, re.M)) >= 5
    assert "exactlyTwo6 (is0 c5a c5b)" in source
    assert "exactlyTwo6 (is1 c5a c5b)" in source
    assert "exactlyTwo6 (is2 c5a c5b)" in source

    print("AUDIT_GENERATION_OK")
    print(f"edge_sha256={sha256(SOL / 'candidate60.edgelist')}")
    print(f"lean_sha256={sha256(LEAN)}")
    print("n=60 m=180 degree=6")
    print("normalized_puncture_colourings=16")
    print("neighbor_profile=2+2+2")
    print("defect_witness_bad_edges=0-5,0-26")


if __name__ == "__main__":
    main()
