#!/usr/bin/env python3
"""Independent hostile replay of certificates.json.

This program knows nothing about how the certificates were generated.  It
checks each branch against the graph and list constraints and rejects missing
possible branches, spurious branches, repeated/out-of-range nodes, assignments
to the deleted vertex, and cycles/forward references.
"""

from __future__ import annotations

from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
EDGE_FILE = HERE / "candidate60.edgelist"
N = 60


def graph() -> list[set[int]]:
    adj = [set() for _ in range(N)]
    seen: set[tuple[int, int]] = set()
    for number, raw in enumerate(EDGE_FILE.read_text().splitlines(), 1):
        fields = raw.split()
        assert len(fields) == 2, f"malformed edge line {number}"
        a, b = map(int, fields)
        assert 0 <= a < b < N and (a, b) not in seen
        seen.add((a, b))
        adj[a].add(b)
        adj[b].add(a)
    assert len(seen) == 180 and {len(x) for x in adj} == {6}
    return adj


def main() -> None:
    adj = graph()
    payload = json.loads((HERE / "certificates.json").read_text())
    cases = payload["cases"]
    assert len(cases) == 21
    total = 0
    for case in cases:
        nodes = case["nodes"]
        masks = case["masks"]
        assert len(masks) == N and masks[0] == 0
        used: set[int] = set()

        def replay(index: int, state: list[int]) -> None:
            assert 0 <= index < len(nodes) and index not in used
            used.add(index)
            node = nodes[index]
            v = node["vertex"]
            children = node["children"]
            assert 0 < v < N and state[v] == -1 and len(children) == 3
            for colour, child in enumerate(children):
                allowed = bool(masks[v] & (1 << colour)) and all(
                    state[w] != colour for w in adj[v] if w != 0
                )
                assert (child >= 0) == allowed
                if child >= 0:
                    assert child < index  # postorder: rejects cycles/forward links
                    nxt = state.copy()
                    nxt[v] = colour
                    replay(child, nxt)

        replay(case["root"], [-1] * N)
        assert len(used) == len(nodes)
        total += len(nodes)
        print(f"PASS {case['name']} nodes={len(nodes)}")
    assert total == 35967
    edge_sha = hashlib.sha256(EDGE_FILE.read_bytes()).hexdigest()
    cert_sha = hashlib.sha256((HERE / "certificates.json").read_bytes()).hexdigest()
    print(f"PASS cases=21 nodes={total}")
    print(f"EDGE_SHA256 {edge_sha}")
    print(f"CERT_SHA256 {cert_sha}")


if __name__ == "__main__":
    main()
