#!/usr/bin/env python3
"""Deterministic structural and positive-certificate audit for candidate60.

This script does not decide non-3-colourability; verify_candidate60.cpp does.
It independently checks the group model, the exact edge and graph6 encodings,
all left translations, the four undirected edge orbits, and the supplied
three-colouring of G-0 (including the q3=2 upper witness).
"""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
N = 60
GENERATORS = (5, 55, 26, 37, 30, 33)
EDGE_SHA256 = "85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c"
G6_SHA256 = "4b6ee8341abb4c6625080e9b6c7a6d7d5b358ee0148c5e8dc8453800d8a6c7ad"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decode(x: int) -> tuple[int, int]:
    return divmod(x, 5)


def encode(e: int, i: int) -> int:
    return (e % 12) * 5 + (i % 5)


def multiply(x: int, y: int) -> int:
    e, i = decode(x)
    f, j = decode(y)
    return encode(e + f, i + pow(2, e, 5) * j)


def read_edges(path: Path) -> tuple[tuple[int, int], ...]:
    edges = []
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        fields = raw.split()
        assert len(fields) == 2, (line_number, raw)
        u, v = map(int, fields)
        assert 0 <= u < v < N, (line_number, u, v)
        edges.append((u, v))
    assert edges == sorted(edges)
    assert len(edges) == len(set(edges)) == 180
    return tuple(edges)


def graph6(edges: tuple[tuple[int, int], ...]) -> str:
    edge_set = set(edges)
    bits = [int((i, j) in edge_set) for j in range(1, N) for i in range(j)]
    chars = [chr(N + 63)]
    for start in range(0, len(bits), 6):
        block = bits[start : start + 6]
        block += [0] * (6 - len(block))
        value = 0
        for bit in block:
            value = 2 * value + bit
        chars.append(chr(value + 63))
    return "".join(chars)


def main() -> None:
    edge_path = ROOT / "candidate60.edgelist"
    g6_path = ROOT / "candidate60.g6"
    colour_path = ROOT / "candidate60_Gminus0.coloring"
    assert sha256(edge_path) == EDGE_SHA256
    assert sha256(g6_path) == G6_SHA256
    edges = read_edges(edge_path)
    edge_set = set(edges)

    # Full finite group audit.
    assert all(multiply(0, x) == x == multiply(x, 0) for x in range(N))
    assert all(
        multiply(multiply(x, y), z) == multiply(x, multiply(y, z))
        for x in range(N)
        for y in range(N)
        for z in range(N)
    )
    inverses = []
    for x in range(N):
        candidates = [y for y in range(N) if multiply(x, y) == multiply(y, x) == 0]
        assert len(candidates) == 1
        inverses.append(candidates[0])
    assert [inverses[s] for s in GENERATORS] == [55, 5, 37, 26, 30, 33]

    rebuilt = {
        tuple(sorted((x, multiply(x, s)))) for x in range(N) for s in GENERATORS
    }
    assert rebuilt == edge_set
    degrees = [0] * N
    adjacency = [set() for _ in range(N)]
    for u, v in edges:
        degrees[u] += 1
        degrees[v] += 1
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert degrees == [6] * N
    reached = {0}
    frontier = [0]
    for u in frontier:
        for v in adjacency[u] - reached:
            reached.add(v)
            frontier.append(v)
    assert len(reached) == N
    assert graph6(edges) + "\n" == g6_path.read_text()

    translations = []
    for a in range(N):
        permutation = tuple(multiply(a, x) for x in range(N))
        assert len(set(permutation)) == N
        image = {
            tuple(sorted((permutation[u], permutation[v]))) for u, v in edges
        }
        assert image == edge_set
        translations.append(permutation)
    assert len({p[0] for p in translations}) == N

    unseen = set(edges)
    orbits = []
    while unseen:
        u, v = min(unseen)
        orbit = {
            tuple(sorted((p[u], p[v]))) for p in translations
        }
        assert orbit <= edge_set
        orbits.append(orbit)
        unseen -= orbit
    representatives = sorted((len(o), min(o)) for o in orbits)
    assert representatives == [(30, (0, 30)), (30, (0, 33)), (60, (0, 5)), (60, (0, 26))]

    # Explicit positive certificate: a proper 3-colouring of G-0.
    tokens = colour_path.read_text().split()
    assert len(tokens) == N and tokens[0] == "-"
    colours = [None] + [int(x) for x in tokens[1:]]
    assert set(colours[1:]) == {0, 1, 2}
    assert all(0 in (u, v) or colours[u] != colours[v] for u, v in edges)
    neighbour_colours = [colours[s] for s in GENERATORS]
    assert sorted(neighbour_colours).count(0) == 2
    assert sorted(neighbour_colours).count(1) == 2
    assert sorted(neighbour_colours).count(2) == 2
    defects = []
    full = [1 if c is None else c for c in colours]
    for u, v in edges:
        if full[u] == full[v]:
            defects.append((u, v))
    assert defects == [(0, 5), (0, 26)]

    print("PASS structural certificate")
    print("order=60 size=180 degree=6 connected_by_generators=true")
    print("left_translations=60 vertex_orbits=1 edge_orbit_sizes=30,30,60,60")
    print("G-minus-0 colouring=valid neighbour_split=2,2,2")
    print("q3 upper witness defects=(0,5),(0,26)")
    print(f"edge_sha256={EDGE_SHA256}")
    print(f"graph6_sha256={G6_SHA256}")


if __name__ == "__main__":
    main()
