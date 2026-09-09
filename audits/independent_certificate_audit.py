#!/usr/bin/env python3
"""Independent structural audit of the generated Dirac-60 search trees.

This does not replace the Lean soundness theorem.  It is a hostile check for
malformed trees and for gaps between the intended 18 cases and the JSON that
was generated.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE_ROOT = HERE.parent
if (PACKAGE_ROOT / "graph" / "candidate60.edgelist").exists():
    EDGE_PATH = PACKAGE_ROOT / "graph" / "candidate60.edgelist"
    CERT_PATH = PACKAGE_ROOT / "lean_search_tree" / "certificates.json"
else:
    ROOT = HERE.parents[2]
    EDGE_PATH = ROOT / "Dirac_k4_order60_solution" / "candidate60.edgelist"
    CERT_PATH = ROOT / "stage3" / "lean_formalizer" / "certificates.json"
N = 60
ALL = 0b111


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def read_graph() -> tuple[list[tuple[int, int]], list[int]]:
    raw = EDGE_PATH.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    expected = "85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c"
    if digest != expected:
        fail(f"edge-list SHA-256 {digest}, expected {expected}")

    edges: list[tuple[int, int]] = []
    adj = [0] * N
    for line_number, line in enumerate(raw.decode().splitlines(), 1):
        fields = line.split()
        if len(fields) != 2:
            fail(f"bad edge line {line_number}")
        u, v = map(int, fields)
        if not 0 <= u < v < N:
            fail(f"noncanonical edge on line {line_number}: {(u, v)}")
        edges.append((u, v))
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    if len(edges) != 180 or len(set(edges)) != 180:
        fail("edge list is not 180 distinct edges")
    if any(x.bit_count() != 6 for x in adj):
        fail("graph is not 6-regular")
    return edges, adj


def audit_case(case: dict, adj: list[int]) -> int:
    nodes = case["nodes"]
    root = case["root"]
    masks = case["masks"]
    if len(masks) != N or any(not isinstance(x, int) or x & ~ALL for x in masks):
        fail(f"{case['name']}: invalid masks")
    if not 0 <= root < len(nodes):
        fail(f"{case['name']}: root outside node array")

    active = ((1 << N) - 1) ^ 1
    assigned = [-1] * N
    visited: set[int] = set()

    def allowed(v: int, color: int) -> bool:
        if not masks[v] & (1 << color):
            return False
        z = adj[v] & active
        while z:
            bit = z & -z
            z ^= bit
            w = bit.bit_length() - 1
            if assigned[w] == color:
                return False
        return True

    def walk(index: int) -> None:
        if index in visited:
            fail(f"{case['name']}: node {index} is reused (DAG/cycle not permitted by this audit)")
        if not 0 <= index < len(nodes):
            fail(f"{case['name']}: child index {index} out of range")
        visited.add(index)
        node = nodes[index]
        v = node["vertex"]
        children = node["children"]
        if not isinstance(v, int) or not 0 <= v < N:
            fail(f"{case['name']}: invalid branch vertex at node {index}")
        if not active & (1 << v):
            fail(f"{case['name']}: inactive branch vertex {v} at node {index}")
        if assigned[v] != -1:
            fail(f"{case['name']}: repeated assigned vertex {v} at node {index}")
        if not isinstance(children, list) or len(children) != 3:
            fail(f"{case['name']}: node {index} does not have three child slots")

        options = [color for color in range(3) if allowed(v, color)]
        for color in range(3):
            child = children[color]
            if color in options:
                if not isinstance(child, int):
                    fail(f"{case['name']}: missing possible color {color} at node {index}")
                if child >= index:
                    fail(f"{case['name']}: nondecreasing child {child} at node {index}")
                assigned[v] = color
                walk(child)
                assigned[v] = -1
            elif child != -1:
                fail(f"{case['name']}: child supplied for impossible color {color} at node {index}")

    walk(root)
    if len(visited) != len(nodes):
        fail(f"{case['name']}: {len(nodes) - len(visited)} unreachable nodes")
    return len(visited)


def main() -> None:
    _, adj = read_graph()
    payload = json.loads(CERT_PATH.read_text())
    cases = payload.get("cases")
    if not isinstance(cases, list) or len(cases) != 21:
        fail("certificate set does not contain exactly 21 cases")

    neighbours = [v for v in range(N) if adj[0] & (1 << v)]
    if neighbours != [5, 26, 30, 33, 37, 55]:
        fail(f"unexpected neighbours of zero: {neighbours}")
    unique_cases = [case for case in cases if case.get("kind") == "unique"]
    missing_cases = [case for case in cases if case.get("kind") == "missing"]
    intended = {(s, color) for s in neighbours for color in range(3)}
    actual = {(case.get("neighbour"), case.get("colour")) for case in unique_cases}
    if actual != intended or len(actual) != len(unique_cases) or len(unique_cases) != 18:
        fail("the 18 neighbour/colour cases are not covered exactly once")
    if len(missing_cases) != 3 or {case.get("colour") for case in missing_cases} != {0, 1, 2}:
        fail("the three missing-colour cases are not covered exactly once")

    total = 0
    for case in cases:
        color = case["colour"]
        masks = case["masks"]
        expected_masks = [ALL] * N
        expected_masks[0] = 0
        if case["kind"] == "unique":
            s = case["neighbour"]
            expected_masks[s] = 1 << color
            for t in neighbours:
                if t != s:
                    expected_masks[t] &= ~(1 << color)
        elif case["kind"] == "missing":
            for t in neighbours:
                expected_masks[t] &= ~(1 << color)
        else:
            fail(f"{case['name']}: unknown case kind")
        if masks != expected_masks:
            fail(f"{case['name']}: masks do not encode the advertised unique-colour case")
        count = audit_case(case, adj)
        total += count
        print(f"PASS {case['name']} nodes={count}")

    print(f"PASS all_cases=21 total_nodes={total}")
    print("SCOPE: 18 unique-neighbour failures plus 3 missing-colour failures")
    print("CONSEQUENCE: every punctured colouring has exact 2+2+2 neighbour counts")


if __name__ == "__main__":
    main()
