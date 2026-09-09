import Mathlib

/-!
# The balanced-puncture mechanism

This file contains no data specific to the order-60 graph.  It isolates the
small theorem that turns a two-per-colour puncture condition into immunity to
single-edge deletion.
-/

universe u

namespace BalancedPuncture

structure FinGraph (V : Type u) where
  adj : V -> V -> Bool
  symm : forall u v, adj u v = adj v u
  loopless : forall v, adj v v = false

variable {V : Type u}

def Proper (G : FinGraph V) {C : Type*} (c : V -> C) : Prop :=
  forall u v, G.adj u v = true -> c u ≠ c v

def ProperExcept [DecidableEq V] (G : FinGraph V) (r : V)
    {C : Type*} (c : V -> C) : Prop :=
  forall u v, G.adj u v = true -> u ≠ r -> v ≠ r -> c u ≠ c v

def ProperAfterEdge [DecidableEq V] (G : FinGraph V) (a b : V)
    {C : Type*} (c : V -> C) : Prop :=
  forall u v, G.adj u v = true ->
    ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) -> c u ≠ c v

/-- Every colour occurs on at least two neighbours of every puncture. -/
def TwoPerColourAtPunctures [DecidableEq V] (G : FinGraph V)
    (C : Type*) : Prop :=
  forall r (c : V -> C), ProperExcept G r c -> forall k : C,
    exists x y, x ≠ y ∧ G.adj r x = true ∧ G.adj r y = true ∧
      c x = k ∧ c y = k

def Colourable (G : FinGraph V) (q : Nat) : Prop :=
  exists c : V -> Fin q, Proper G c

def ColourableExcept [DecidableEq V] (G : FinGraph V) (q : Nat)
    (r : V) : Prop :=
  exists c : V -> Fin q, ProperExcept G r c

def KVertexCritical [DecidableEq V] (G : FinGraph V) (k : Nat) : Prop :=
  Colourable G k ∧ ¬ Colourable G (k - 1) ∧
    forall r, ColourableExcept G (k - 1) r

def FourVertexCritical [DecidableEq V] (G : FinGraph V) : Prop :=
  KVertexCritical G 4

/-- `G-e` is not 3-colourable for every edge `e`. -/
def EdgeImmuneAt [DecidableEq V] (G : FinGraph V) (k : Nat) : Prop :=
  forall a b, G.adj a b = true ->
    ¬ (exists c : V -> Fin (k - 1), ProperAfterEdge G a b c)

def EdgeImmuneAtFour [DecidableEq V] (G : FinGraph V) : Prop :=
  EdgeImmuneAt G 4

theorem twoPerColour_not_colourable [DecidableEq V] [Nonempty V] (G : FinGraph V)
    (h : TwoPerColourAtPunctures G (Fin 3)) : ¬ Colourable G 3 := by
  rintro ⟨c, hc⟩
  classical
  let r : V := Classical.choice (inferInstance : Nonempty V)
  have hp : ProperExcept G r c := by
    intro u v huv _ _
    exact hc u v huv
  obtain ⟨x, _y, _hxy, hrx, _hry, hcx, _hcy⟩ := h r c hp (c r)
  exact hc r x hrx hcx.symm

/--
The central decoupling lemma.  If every proper colouring of every vertex
puncture uses every colour at least twice around the hole, then deleting one
edge can never make the graph colourable with those colours.
-/
theorem twoPerColour_edgeImmune [DecidableEq V] (G : FinGraph V)
    (h : TwoPerColourAtPunctures G (Fin 3)) : EdgeImmuneAtFour G := by
  intro a b hab
  rintro ⟨c, hc⟩
  have habne : a ≠ b := by
    intro heq
    subst b
    simpa [G.loopless a] using hab
  have hp : ProperExcept G a c := by
    intro u v huv hua hva
    apply hc u v huv
    intro hdeleted
    rcases hdeleted with h | h
    · exact hua h.1
    · exact hva h.2
  obtain ⟨x, y, hxy, hax, hay, hcx, hcy⟩ := h a c hp (c a)
  by_cases hxb : x = b
  · have hyb : y ≠ b := by
      intro hyb
      apply hxy
      exact hxb.trans hyb.symm
    have hkeep : ¬ ((a = a ∧ y = b) ∨ (a = b ∧ y = a)) := by
      intro hd
      rcases hd with hd | hd
      · exact hyb hd.2
      · exact habne hd.1
    exact hc a y hay hkeep hcy.symm
  · have hkeep : ¬ ((a = a ∧ x = b) ∨ (a = b ∧ x = a)) := by
      intro hd
      rcases hd with hd | hd
      · exact hxb hd.2
      · exact habne hd.1
    exact hc a x hax hkeep hcx.symm

theorem balanced_puncture_decoupling [DecidableEq V] [Nonempty V] (G : FinGraph V)
    (h4 : Colourable G 4)
    (hdel : forall r, ColourableExcept G 3 r)
    (hbal : TwoPerColourAtPunctures G (Fin 3)) :
    FourVertexCritical G ∧ EdgeImmuneAtFour G := by
  constructor
  · exact ⟨h4, twoPerColour_not_colourable G hbal, hdel⟩
  · exact twoPerColour_edgeImmune G hbal

end BalancedPuncture
