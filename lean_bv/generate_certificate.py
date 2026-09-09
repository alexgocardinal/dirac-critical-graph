#!/usr/bin/env python3
"""Generate the repetitive, reviewable Lean certificate for the order-60 graph.

The generated theorem statements deliberately unroll all finite data.  This
keeps `bv_decide` on a quantifier-free Boolean formula and makes the trusted
Lean portion independent of the discovery/search programs.
"""

from __future__ import annotations

from pathlib import Path


HERE = Path(__file__).resolve().parent
PACKAGE_GRAPH = HERE.parent / "graph"
LEGACY_GRAPH = HERE.parent.parent / "Dirac_k4_order60_solution"
SOLUTION = PACKAGE_GRAPH if PACKAGE_GRAPH.exists() else LEGACY_GRAPH


def load_edges() -> list[tuple[int, int]]:
    edges: list[tuple[int, int]] = []
    for line in (SOLUTION / "candidate60.edgelist").read_text().splitlines():
        if line.strip():
            u, v = map(int, line.split())
            edges.append((u, v))
    assert len(edges) == 180
    assert all(0 <= u < v < 60 for u, v in edges)
    assert len(set(edges)) == len(edges)
    return edges


def load_witnesses() -> list[list[int]]:
    rows: list[list[int]] = []
    for expected, line in enumerate(
        (SOLUTION / "audits" / "vertex_witnesses.txt").read_text().splitlines()
    ):
        label, word = line.split()
        assert int(label) == expected
        assert len(word) == 60 and word[expected] == "-"
        row = [0 if ch == "-" else int(ch) for ch in word]
        assert all(x in (0, 1, 2) for x in row)
        rows.append(row)
    assert len(rows) == 60
    return rows


def wrapped(items: list[str], indent: str = "    ", width: int = 92) -> str:
    lines: list[str] = []
    current = indent
    for item in items:
        sep = " " if current.strip() else ""
        if len(current) + len(sep) + len(item) > width and current.strip():
            lines.append(current.rstrip())
            current = indent + item
        else:
            current += sep + item
    if current.strip():
        lines.append(current.rstrip())
    return "\n".join(lines)


def bool_binders() -> str:
    names = [f"c{v}{bit}" for v in range(60) for bit in ("a", "b")]
    # Several binders avoid parser/elaborator stress from one enormous binder.
    groups = [names[i : i + 12] for i in range(0, len(names), 12)]
    return "\n".join("  (" + " ".join(g) + " : Bool)" for g in groups)


def code(v: int) -> str:
    return f"c{v}a c{v}b"


def valid(v: int) -> str:
    return f"validCode {code(v)}"


def same(u: int, v: int) -> str:
    return f"sameCode {code(u)} {code(v)}"


def proper(u: int, v: int) -> str:
    return f"!({same(u, v)})"


def list_expr(items: list[str], indent: str = "    ") -> str:
    if not items:
        return "[]"
    lines = []
    for i in range(0, len(items), 4):
        chunk = items[i : i + 4]
        prefix = "[" if i == 0 else " "
        suffix = "," if i + 4 < len(items) else "]"
        lines.append(indent + prefix + ", ".join(chunk) + suffix)
    return "\n".join(lines)


def allb(items: list[str], indent: str = "    ") -> str:
    return "allB\n" + list_expr(items, indent)


def exact_two(args: list[str]) -> str:
    assert len(args) == 6
    return "exactlyTwo6 " + " ".join(f"({arg})" for arg in args)


def color_test(v: int, color: int) -> str:
    return f"is{color} {code(v)}"


def template_constraints(template: str) -> list[str]:
    assert len(template) == 60 and template[0] == "-"
    out: list[str] = []
    for v, ch in enumerate(template):
        if ch in "012":
            out.append(color_test(v, int(ch)))
        elif ch == "*":
            if v in (2, 41):
                # State the domain positively so the invalid code 11 cannot
                # satisfy the right-hand side of the iff.
                out.append(
                    f"(({color_test(v, 1)}) || ({color_test(v, 2)}))"
                )
            elif v in (3, 24):
                out.append(
                    f"(({color_test(v, 0)}) || ({color_test(v, 1)}))"
                )
            else:
                raise AssertionError(v)
        elif ch != "-":
            raise AssertionError(ch)
    return out


def lean_edges(edges: list[tuple[int, int]]) -> str:
    items = [f"({u}, {v})" for u, v in edges]
    nat_edges = "def edges : List (Nat × Nat) :=\n" + list_expr(items, "  ")
    fin_edges = "def graphEdges : List (V × V) :=\n" + list_expr(items, "  ")
    return nat_edges + "\n\n" + fin_edges


def lean_witnesses(rows: list[list[int]]) -> str:
    rendered_rows = ["#[" + ", ".join(map(str, row)) + "]" for row in rows]
    lines = ["def vertexWitnesses : Array (Array Nat) := #["]
    for i, row in enumerate(rendered_rows):
        comma = "," if i + 1 < len(rendered_rows) else ""
        lines.append(f"  {row}{comma}")
    lines.append("]")
    return "\n".join(lines)


def generate() -> None:
    edges = load_edges()
    witnesses = load_witnesses()
    minus0 = [(u, v) for u, v in edges if u != 0 and v != 0]
    neighbours = [v if u == 0 else u for u, v in edges if u == 0 or v == 0]
    assert neighbours == [5, 26, 30, 33, 37, 55]
    template = "-0**21102120110012022002*1110202021202100*022201111120202021"

    binders = bool_binders()
    valid_1_59 = [valid(v) for v in range(1, 60)]
    proper_minus0 = [proper(u, v) for u, v in minus0]
    conflicts = [same(u, v) for u, v in edges]
    balance_terms = [
        exact_two([color_test(v, col) for v in neighbours]) for col in range(3)
    ]
    normalized_terms = [color_test(1, 0), color_test(6, 1)]
    template_terms = template_constraints(template)
    bit_arguments = []
    for v in range(60):
        bit_arguments.extend([f"(bitA (c {v}))", f"(bitB (c {v}))"])
    bit_application = "\n".join(
        "    " + " ".join(bit_arguments[i : i + 8])
        for i in range(0, len(bit_arguments), 8)
    )

    source = f'''import Mathlib.Tactic

/-!
# A proof-producing certificate for the order-60 Dirac graph

The graph data and all finite Boolean constraints are explicit below.  The
three main negative results use `bv_decide`, whose SAT proof is replayed by
Lean's verified reflection pipeline.  The precise axioms used by the selected
toolchain are printed at the end of this file.  `native_decide` is used only
for positive concrete witness replay; it is never used to establish an
UNSAT/non-colourability claim.

Color codes are `00`, `10`, and `01`; `11` is invalid.  Thus two Boolean
variables encode one of three colours without using an untrusted parser.
-/

namespace Dirac60

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def validCode (a b : Bool) : Bool := !(a && b)

def sameCode (a b x y : Bool) : Bool := (a == x) && (b == y)

def is0 (a b : Bool) : Bool := (!a) && (!b)
def is1 (a b : Bool) : Bool := a && (!b)
def is2 (a b : Bool) : Bool := (!a) && b

def allB : List Bool → Bool
  | [] => true
  | x :: xs => x && allB xs

def atMostOneAux : Bool → List Bool → Bool
  | _, [] => true
  | seen, x :: xs => (!(seen && x)) && atMostOneAux (seen || x) xs

def atMostOne (xs : List Bool) : Bool := atMostOneAux false xs

def exactlyTwo6 (a b c d e f : Bool) : Bool :=
  ((a && b) && (!c && !d && !e && !f)) ||
  ((a && c) && (!b && !d && !e && !f)) ||
  ((a && d) && (!b && !c && !e && !f)) ||
  ((a && e) && (!b && !c && !d && !f)) ||
  ((a && f) && (!b && !c && !d && !e)) ||
  ((b && c) && (!a && !d && !e && !f)) ||
  ((b && d) && (!a && !c && !e && !f)) ||
  ((b && e) && (!a && !c && !d && !f)) ||
  ((b && f) && (!a && !c && !d && !e)) ||
  ((c && d) && (!a && !b && !e && !f)) ||
  ((c && e) && (!a && !b && !d && !f)) ||
  ((c && f) && (!a && !b && !d && !e)) ||
  ((d && e) && (!a && !b && !c && !f)) ||
  ((d && f) && (!a && !b && !c && !e)) ||
  ((e && f) && (!a && !b && !c && !d))

/- Every proper three-colouring of `G - 0` gives each colour exactly twice
on `N(0) = {{5,26,30,33,37,55}}`.  No normalization is assumed. -/
theorem puncture_balance_universal
{binders} :
  let premise :=
    ({allb(valid_1_59, '      ')}) &&
    ({allb(proper_minus0, '      ')})
  let balanced :=
    {balance_terms[0]} &&
    {balance_terms[1]} &&
    {balance_terms[2]}
  ((!premise) || balanced) = true := by
  simp [validCode, sameCode, is0, is1, is2, allB, exactlyTwo6]
  bv_decide

/- With `c(1)=0` and `c(6)=1`, the punctured colourings are exactly the
16 assignments described by the four independent stars in the paper. -/
theorem normalized_puncture_classifier
{binders} :
  let normalizedProper :=
    ({allb(valid_1_59, '      ')}) &&
    ({allb(proper_minus0, '      ')}) &&
    ({allb(normalized_terms, '      ')})
  let template :=
    {allb(template_terms, '      ')}
  (normalizedProper == template) = true := by
  simp [validCode, sameCode, is0, is1, is2, allB]
  bv_decide

/- Equivalently, no valid three-colour assignment has zero or one bad edge.
This is the compact Boolean form of `q₃(G) ≥ 2`, and directly implies that
deleting any single edge leaves the graph non-three-colourable. -/
theorem q3_ge_two_encoded
{binders} :
  (({allb([valid(v) for v in range(60)], '      ')}) &&
    atMostOne
{list_expr(conflicts, '      ')}) = false := by
  simp (config := {{ maxSteps := 1000000 }}) only
    [validCode, sameCode, allB, atMostOne, atMostOneAux]
  bv_decide

abbrev V := Fin 60

{lean_edges(edges)}

def graphEdgesAsNats : List (Nat × Nat) :=
  graphEdges.map fun e => (e.1.val, e.2.val)

theorem edge_tables_agree : graphEdgesAsNats = edges := by
  native_decide

{lean_witnesses(witnesses)}

def edgeOKAway (deleted : Nat) (row : Array Nat) (e : Nat × Nat) : Bool :=
  let (u, v) := e
  (u == deleted) || (v == deleted) ||
    ((decide (row.getD u 3 < 3)) && (decide (row.getD v 3 < 3)) &&
      !(row.getD u 3 == row.getD v 3))

def witnessRowOK (deleted : Nat) : Bool :=
  match vertexWitnesses[deleted]? with
  | none => false
  | some row =>
      (row.size == 60) &&
      allB (edges.map (edgeOKAway deleted row))

def allVertexWitnessesOK : Bool :=
  allB ((List.range 60).map witnessRowOK)

/- Positive certificate only: sixty explicitly stored colourings, one for
each deleted vertex. -/
theorem all_vertex_deletion_witnesses : allVertexWitnessesOK = true := by
  native_decide

def defectColouring : Array Nat :=
  #[1, 0, 1, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2,
    2, 0, 0, 2, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0,
    0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1]

def defectCount : Nat :=
  (edges.filter fun e =>
    defectColouring.getD e.1 3 == defectColouring.getD e.2 3).length

def defectWitnessWellFormed : Bool :=
  (defectColouring.size == 60) &&
    allB (defectColouring.toList.map fun x => decide (x < 3))

/- Positive certificate for the matching upper bound `q₃(G) ≤ 2`. -/
theorem q3_le_two_witness :
    defectWitnessWellFormed = true ∧ defectCount = 2 := by
  native_decide

/-! ## Proposition-level semantic bridge -/

inductive Colour3 where
  | red | green | blue
  deriving DecidableEq, Repr

def bitA : Colour3 → Bool
  | .red => false
  | .green => true
  | .blue => false

def bitB : Colour3 → Bool
  | .red => false
  | .green => false
  | .blue => true

@[simp] theorem valid_encoding (x : Colour3) :
    validCode (bitA x) (bitB x) = true := by
  cases x <;> decide

@[simp] theorem same_encoding (x y : Colour3) :
    sameCode (bitA x) (bitB x) (bitA y) (bitB y) = decide (x = y) := by
  cases x <;> cases y <;> decide

@[simp] theorem is0_encoding (x : Colour3) :
    is0 (bitA x) (bitB x) = decide (x = .red) := by
  cases x <;> decide

@[simp] theorem is1_encoding (x : Colour3) :
    is1 (bitA x) (bitB x) = decide (x = .green) := by
  cases x <;> decide

@[simp] theorem is2_encoding (x : Colour3) :
    is2 (bitA x) (bitB x) = decide (x = .blue) := by
  cases x <;> decide

def conflicts (c : V → Colour3) : List Bool :=
  graphEdges.map fun e => decide (c e.1 = c e.2)

def proper3 (c : V → Colour3) : Bool :=
  allB ((conflicts c).map fun x => !x)

def ThreeColourable : Prop := ∃ c : V → Colour3, proper3 c = true

/- This theorem is the semantic form of `q3_ge_two_encoded`: the quantified
object is now an ordinary map from the 60 graph vertices to an inductive
three-element colour type. -/
theorem no_at_most_one_bad_edge (c : V → Colour3) :
    atMostOne (conflicts c) = false := by
  have h := q3_ge_two_encoded
{bit_application}
  simp only [valid_encoding, allB] at h
  simpa [conflicts, graphEdges] using h

theorem atMostOne_of_noConflicts :
    ∀ xs : List Bool,
      allB (xs.map fun x => !x) = true → atMostOne xs = true
  | [], _ => by decide
  | false :: xs, h => by
      have ih := atMostOne_of_noConflicts xs
      simpa [allB, atMostOne, atMostOneAux] using ih (by simpa [allB] using h)
  | true :: xs, h => by
      simp [allB] at h

theorem not_three_colourable : ¬ ThreeColourable := by
  rintro ⟨c, hc⟩
  have ha : atMostOne (conflicts c) = true :=
    atMostOne_of_noConflicts (conflicts c) hc
  have hn := no_at_most_one_bad_edge c
  rw [ha] at hn
  cases hn

/- A colouring of `G-e` is exactly a colouring of `G` with at most one bad
edge, because the only allowed conflict is the deleted edge. -/
def ThreeColourableAfterDeletingAtMostOneEdge : Prop :=
  ∃ c : V → Colour3, atMostOne (conflicts c) = true

theorem no_single_edge_deletion_is_three_colourable :
    ¬ ThreeColourableAfterDeletingAtMostOneEdge := by
  rintro ⟨c, hc⟩
  have hn := no_at_most_one_bad_edge c
  rw [hc] at hn
  cases hn

def properAway (deleted : V) (c : V → Colour3) : Bool :=
  allB (graphEdges.map fun e =>
    decide (e.1 = deleted) || decide (e.2 = deleted) ||
      !(decide (c e.1 = c e.2)))

def colour3OfNat : Nat → Colour3
  | 0 => .red
  | 1 => .green
  | _ => .blue

def witnessColour (deleted u : V) : Colour3 :=
  colour3OfNat ((vertexWitnesses.getD deleted.val #[]).getD u.val 0)

/- Concrete semantic witness for every vertex deletion. -/
theorem every_vertex_deletion_has_displayed_colouring :
    ∀ deleted : V, properAway deleted (witnessColour deleted) = true := by
  native_decide

theorem every_vertex_deletion_is_three_colourable :
    ∀ deleted : V, ∃ c : V → Colour3, properAway deleted c = true := by
  intro deleted
  exact ⟨witnessColour deleted,
    every_vertex_deletion_has_displayed_colouring deleted⟩

def properAwayZero (c : V → Colour3) : Bool := properAway 0 c

def balancedAtZero (c : V → Colour3) : Bool :=
  exactlyTwo6
      (decide (c 5 = .red)) (decide (c 26 = .red))
      (decide (c 30 = .red)) (decide (c 33 = .red))
      (decide (c 37 = .red)) (decide (c 55 = .red)) &&
  exactlyTwo6
      (decide (c 5 = .green)) (decide (c 26 = .green))
      (decide (c 30 = .green)) (decide (c 33 = .green))
      (decide (c 37 = .green)) (decide (c 55 = .green)) &&
  exactlyTwo6
      (decide (c 5 = .blue)) (decide (c 26 = .blue))
      (decide (c 30 = .blue)) (decide (c 33 = .blue))
      (decide (c 37 = .blue)) (decide (c 55 = .blue))

/- The encoded theorem `puncture_balance_universal` above is the compact
certificate for puncture balance.  Its proposition-level graph formulation is
proved in the independent `lean_search_tree` development.  Keeping that bridge
out of this compact file avoids asking `simp` to reassociate two generated
180-entry Boolean lists. -/

inductive Colour4 where
  | red | green | blue | extra
  deriving DecidableEq, Repr

def embed3 : Colour3 → Colour4
  | .red => .red
  | .green => .green
  | .blue => .blue

def displayedFourColouring (u : V) : Colour4 :=
  if u = 0 then .extra else embed3 (witnessColour 0 u)

def proper4 (c : V → Colour4) : Bool :=
  allB (graphEdges.map fun e => !(decide (c e.1 = c e.2)))

theorem displayed_four_colouring_is_proper :
    proper4 displayedFourColouring = true := by
  native_decide

structure CertifiedDiracResult : Prop where
  notThreeColourable : ¬ ThreeColourable
  fourColouring : ∃ c : V → Colour4, proper4 c = true
  vertexDeletions : ∀ deleted : V,
    ∃ c : V → Colour3, properAway deleted c = true
  noOneEdgeRepair : ¬ ThreeColourableAfterDeletingAtMostOneEdge

theorem certified_dirac_result : CertifiedDiracResult where
  notThreeColourable := not_three_colourable
  fourColouring := ⟨displayedFourColouring,
    displayed_four_colouring_is_proper⟩
  vertexDeletions := every_vertex_deletion_is_three_colourable
  noOneEdgeRepair := no_single_edge_deletion_is_three_colourable

/- These commands make the exact trust footprint visible in every build log.
In particular, they distinguish the `bv_decide` theorems from the positive
`native_decide` witness replays. -/
#print axioms puncture_balance_universal
#print axioms normalized_puncture_classifier
#print axioms q3_ge_two_encoded
#print axioms no_at_most_one_bad_edge
#print axioms certified_dirac_result

end Dirac60
'''

    (HERE / "Dirac60").mkdir(parents=True, exist_ok=True)
    (HERE / "Dirac60" / "Certificate.lean").write_text(source)


if __name__ == "__main__":
    generate()
