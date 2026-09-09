import BalancedPuncture

/-!
# The order-60 Cayley graph

Vertices are pairs `(e,i) in Z/12 x Z/5`, encoded by `5*e+i`.  Multiplication
is `(e,i)(f,j) = (e+f, i+2^e*j)`.  The inverse-closed connection set is
`{5,55,26,37,30,33}`.

The large generated file `Dirac60Certificates.lean` contains only search-tree
data.  The semantic checker and its soundness theorem are in this file.
-/

open BalancedPuncture

namespace Dirac60

abbrev V := Fin 60

/- Lean deliberately does not install finite universal quantification as a
global decidability instance.  The concrete witness checks below quantify only
over `Fin n`, so provide that computable instance locally for this module. -/
local instance finDecidableForall {n : Nat} {p : Fin n → Prop}
    [∀ i, Decidable (p i)] : Decidable (∀ i, p i) :=
  Fintype.decidableForallFintype

def vertex (n : Nat) : V := ⟨n % 60, Nat.mod_lt _ (by decide)⟩

def action (e : Nat) : Nat :=
  match e % 4 with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 3

def mul (x y : V) : V :=
  vertex ((((x.val / 5 + y.val / 5) % 12) * 5) +
    ((x.val % 5 + action (x.val / 5) * (y.val % 5)) % 5))

def inv (x : V) : V :=
  let e := x.val / 5
  let i := x.val % 5
  let f := (12 - e) % 12
  vertex (5 * f + (5 - ((action f * i) % 5)) % 5)

def generators : List V := [5, 55, 26, 37, 30, 33]

def adjacent (x y : V) : Bool :=
  generators.any (fun s => mul x s == y)

def G : FinGraph V where
  adj := adjacent
  symm := by native_decide
  loopless := by native_decide

/-! ## Explicit positive witnesses -/

-- Vertex zero is irrelevant in this punctured colouring and is assigned 0.
def baseColourData : Array (Fin 3) := #[
  0, 0, 2, 0, 2, 1, 1, 0, 2, 1,
  2, 0, 1, 1, 0, 0, 1, 2, 0, 2,
  2, 0, 0, 2, 1, 1, 1, 1, 0, 2,
  0, 2, 0, 2, 1, 2, 0, 2, 1, 0,
  0, 1, 0, 2, 2, 2, 0, 1, 1, 1,
  1, 1, 2, 0, 2, 0, 2, 0, 2, 1]

def baseColour (x : V) : Fin 3 := baseColourData[x.val]!

def shiftToZero (r x : V) : V := mul (inv r) x

def punctureColour (r x : V) : Fin 3 := baseColour (shiftToZero r x)

def liftColour (k : Fin 3) : Fin 4 :=
  ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩

def fourColour (x : V) : Fin 4 :=
  if x = 0 then 3 else liftColour (baseColour x)

theorem baseColour_is_proper : ProperExcept G 0 baseColour := by
  simp only [ProperExcept]
  native_decide

theorem punctureColour_is_always_proper :
    forall r : V, ProperExcept G r (punctureColour r) := by
  simp only [ProperExcept]
  native_decide

theorem every_vertex_deletion_is_three_colourable :
    forall r : V, ColourableExcept G 3 r := by
  intro r
  exact ⟨punctureColour r, punctureColour_is_always_proper r⟩

theorem graph_is_four_colourable : Colourable G 4 := by
  refine ⟨fourColour, ?_⟩
  simp only [Proper]
  native_decide

/-! ## A proof-producing finite list-colouring checker -/

structure ListProblem where
  active : V -> Bool
  permits : V -> Fin 3 -> Bool

def SearchProper (p : ListProblem) (c : V -> Fin 3) : Prop :=
  (forall v, p.active v = true -> p.permits v (c v) = true) ∧
  (forall u v, p.active u = true -> p.active v = true ->
    adjacent u v = true -> c u ≠ c v)

abbrev State := V -> Option (Fin 3)

def Extends (st : State) (c : V -> Fin 3) : Prop :=
  forall v k, st v = some k -> c v = k

def Compatible (p : ListProblem) (st : State) (v : V) (k : Fin 3) : Prop :=
  p.active v = true ∧ p.permits v k = true ∧
    forall w, p.active w = true -> adjacent v w = true -> st w ≠ some k

inductive SearchTree where
  | closed
  | branch (vertex : V) (child0 child1 child2 : SearchTree)

def Valid (p : ListProblem) : SearchTree -> State -> Prop
  | .closed, _ => False
  | .branch v t0 t1 t2, st =>
      p.active v = true ∧ st v = none ∧
      (Compatible p st v 0 ->
        Valid p t0 (Function.update st v (some 0))) ∧
      (Compatible p st v 1 ->
        Valid p t1 (Function.update st v (some 1))) ∧
      (Compatible p st v 2 ->
        Valid p t2 (Function.update st v (some 2)))

def emptyState : State := fun _ => none

theorem emptyState_extends (c : V -> Fin 3) : Extends emptyState c := by
  intro v k h
  simp [emptyState] at h

theorem extends_update {st : State} {c : V -> Fin 3} {v : V}
    (h : Extends st c) :
    Extends (Function.update st v (some (c v))) c := by
  intro w k hw
  by_cases hwv : w = v
  · subst w
    simpa using hw
  · rw [Function.update_noteq hwv] at hw
    exact h w k hw

theorem compatible_of_colouring {p : ListProblem} {st : State}
    {c : V -> Fin 3} (hc : SearchProper p c) (he : Extends st c)
    {v : V} (hv : p.active v = true) : Compatible p st v (c v) := by
  refine ⟨hv, hc.1 v hv, ?_⟩
  intro w hw hadj hstate
  have hcw : c w = c v := he w (c v) hstate
  exact hc.2 v w hv hw hadj hcw.symm

/-- Soundness of the generated search-tree format. -/
theorem valid_no_extension {p : ListProblem} {t : SearchTree} {st : State}
    (hvalid : Valid p t st) :
    ¬ (exists c, SearchProper p c ∧ Extends st c) := by
  induction t generalizing st with
  | closed => exact False.elim (by simpa [Valid] using hvalid)
  | branch v t0 t1 t2 ih0 ih1 ih2 =>
      simp only [Valid] at hvalid
      rcases hvalid with ⟨hv, hnone, h0, h1, h2⟩
      rintro ⟨c, hc, he⟩
      have hcomp := compatible_of_colouring hc he hv
      by_cases hcv0 : c v = 0
      · apply ih0 (h0 (by simpa [hcv0] using hcomp))
        exact ⟨c, hc, by
          simpa [hcv0] using (extends_update (v := v) he)⟩
      · by_cases hcv1 : c v = 1
        · apply ih1 (h1 (by simpa [hcv1] using hcomp))
          exact ⟨c, hc, by
            simpa [hcv1] using (extends_update (v := v) he)⟩
        · have hcv2 : c v = 2 := by omega
          apply ih2 (h2 (by simpa [hcv2] using hcomp))
          exact ⟨c, hc, by
            simpa [hcv2] using (extends_update (v := v) he)⟩

theorem valid_no_colouring {p : ListProblem} {t : SearchTree}
    (hvalid : Valid p t emptyState) :
    ¬ (exists c, SearchProper p c) := by
  intro hc
  obtain ⟨c, hc⟩ := hc
  exact valid_no_extension hvalid ⟨c, hc, emptyState_extends c⟩

/-! ## The 21 certificate instances -/

def puncturedActive (v : V) : Bool := decide (v ≠ 0)

def missingProblem (k : Fin 3) : ListProblem where
  active := puncturedActive
  permits := fun v j =>
    if adjacent 0 v then decide (j ≠ k) else true

def uniqueProblem (s : V) (k : Fin 3) : ListProblem where
  active := puncturedActive
  permits := fun v j =>
    if v = s then decide (j = k)
    else if adjacent 0 v then decide (j ≠ k)
    else true

/- The generated certificate declarations are imported by `Dirac60Result`. -/

/-! ## Concrete translations, checked over all 60 vertices -/

def unshift (r x : V) : V := mul r x

theorem unshift_zero : forall r : V, unshift r 0 = r := by native_decide

theorem unshift_injective : forall r : V, Function.Injective (unshift r) := by
  native_decide

theorem unshift_preserves_adjacency : forall r u v : V,
    adjacent (unshift r u) (unshift r v) = adjacent u v := by
  native_decide

end Dirac60
