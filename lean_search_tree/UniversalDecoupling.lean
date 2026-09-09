import Mathlib.Tactic

/-!
# Conditional logical closure of the Universal Decoupling Theorem

This theorem deliberately keeps the two external graph-theoretic inputs as
parameters.  In particular, the claimed Jensen construction for every
`k >= 5` is not inserted as an axiom.  `orderFour` is discharged by
`Dirac60.order60_solution` after choosing an ambient encoding of finite
graphs; `jensenGeFive` and `lowChromaticObstruction` must be supplied from
their separately formalized mathematical proofs.
-/

namespace UniversalDecoupling

variable {Graph : Type*}

def ExistsAt
    (chromaticNumber : Graph -> Nat)
    (vertexCritical edgeImmune : Graph -> Prop)
    (k : Nat) : Prop :=
  exists G : Graph,
    chromaticNumber G = k ∧ vertexCritical G ∧ edgeImmune G

theorem iff_ge_four
    (chromaticNumber : Graph -> Nat)
    (vertexCritical edgeImmune : Graph -> Prop)
    (orderFour : ExistsAt chromaticNumber vertexCritical edgeImmune 4)
    (jensenGeFive : forall k : Nat, 5 ≤ k ->
      ExistsAt chromaticNumber vertexCritical edgeImmune k)
    (lowChromaticObstruction : forall k : Nat, 2 ≤ k ->
      ExistsAt chromaticNumber vertexCritical edgeImmune k -> 4 ≤ k) :
    forall k : Nat, 2 ≤ k ->
      (ExistsAt chromaticNumber vertexCritical edgeImmune k ↔ 4 ≤ k) := by
  intro k hk2
  constructor
  · exact lowChromaticObstruction k hk2
  · intro hk
    by_cases h4 : k = 4
    · simpa [h4] using orderFour
    · have h5 : 5 ≤ k := by omega
      exact jensenGeFive k h5

end UniversalDecoupling
