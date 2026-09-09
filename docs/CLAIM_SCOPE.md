# Claim scope

## Lean-checked claim

For the explicit `Fin 60` Cayley graph defined in the repository:

```lean
Dirac60.order60_solution :
  FourVertexCritical G ∧ EdgeImmuneAtFour G
```

This says the graph is 4-colourable but not 3-colourable, every vertex-deleted
graph is 3-colourable, and no deletion of a single edge makes the graph
3-colourable.

The reported final axiom footprint is:

```text
[propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
```

There is no `sorryAx`.

## Conventional mathematical consequence

For `k>=2`, let `D(k)` mean that some finite `k`-vertex-critical graph is
immune to every single-edge deletion. Combining:

1. the Lean-checked order-60 graph for `k=4`;
2. the elementary obstructions at `k=2,3`; and
3. Jensen's published existence theorem for every `k>=5`;

gives `D(k) <-> k>=4`.

## What is not claimed

- The repository does not formalize Jensen's infinite family.
- It does not prove that every vertex-critical graph with chromatic number at
  least four is edge-immune. That pointwise statement is false; `K4` is a
  counterexample.
- It does not claim immunity after deleting arbitrary sets of edges.
- It does not claim peer-reviewed or community acceptance.
- It does not eliminate the `Lean.ofReduceBool` native-evaluation trust base.

