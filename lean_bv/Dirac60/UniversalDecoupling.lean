import Mathlib.Tactic

/-!
# Logical glue for the Universal Decoupling Theorem

This file proves only the final quantifier/arithmetic step.  The order-4
construction, the known constructions for every `k >= 5`, and impossibility
for `k <= 3` remain explicit hypotheses.  In particular, Jensen's theorem is
*not* introduced as a Lean axiom or silently assumed.
-/

namespace UniversalDecoupling

variable {Graph : Type*}

def ExistsAt
    (chromaticNumber : Graph → Nat)
    (vertexCritical edgeImmune : Graph → Prop)
    (k : Nat) : Prop :=
  ∃ G : Graph,
    chromaticNumber G = k ∧ vertexCritical G ∧ edgeImmune G

/- Once the three mathematical inputs are supplied, existence occurs exactly
at the chromatic numbers `k >= 4`. -/
theorem iff_ge_four
    (chromaticNumber : Graph → Nat)
    (vertexCritical edgeImmune : Graph → Prop)
    (orderFour :
      ExistsAt chromaticNumber vertexCritical edgeImmune 4)
    (jensenGeFive : ∀ k : Nat, 5 ≤ k →
      ExistsAt chromaticNumber vertexCritical edgeImmune k)
    (lowChromaticObstruction : ∀ k : Nat, 2 ≤ k →
      ExistsAt chromaticNumber vertexCritical edgeImmune k → 4 ≤ k) :
    ∀ k : Nat, 2 ≤ k →
      (ExistsAt chromaticNumber vertexCritical edgeImmune k ↔ 4 ≤ k) := by
  intro k
  intro hk2
  constructor
  · exact lowChromaticObstruction k hk2
  · intro hk
    by_cases h4 : k = 4
    · simpa [h4] using orderFour
    · have h5 : 5 ≤ k := by omega
      exact jensenGeFive k h5

#print axioms iff_ge_four

end UniversalDecoupling
