import Dirac60Certificates

/-!
# Certified result for the order-60 graph

The 21 `native_decide` calls below do not search for colourings.  They only
replay finite trees in the proof-producing checker whose soundness theorem is
`Dirac60.valid_no_extension`.
-/

open BalancedPuncture

namespace Dirac60

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/- Computable decision procedures used only to replay the finite certificate
trees.  Lean does not install finite universal quantification as a global
instance, and `Valid` is a recursive proposition rather than an inductive
predicate with an automatically generated decision procedure. -/
local instance finDecidableForallResult {n : Nat} {p : Fin n → Prop}
    [∀ i, Decidable (p i)] : Decidable (∀ i, p i) :=
  Fintype.decidableForallFintype

local instance compatibleIsDecidable (p : ListProblem) (st : State)
    (v : V) (k : Fin 3) : Decidable (Compatible p st v k) := by
  unfold Compatible
  infer_instance

private def validDecidable (p : ListProblem) :
    (t : SearchTree) → (st : State) → Decidable (Valid p t st)
  | .closed, _ => isFalse (by simp [Valid])
  | .branch v t0 t1 t2, st => by
      letI : Decidable (Valid p t0 (Function.update st v (some 0))) :=
        validDecidable p t0 _
      letI : Decidable (Valid p t1 (Function.update st v (some 1))) :=
        validDecidable p t1 _
      letI : Decidable (Valid p t2 (Function.update st v (some 2))) :=
        validDecidable p t2 _
      unfold Valid
      infer_instance

local instance validIsDecidable (p : ListProblem) (t : SearchTree)
    (st : State) : Decidable (Valid p t st) := validDecidable p t st

/-! ## Replay the 18 no-unique-colour certificates -/

theorem dupFail_s0_c0_valid :
    Valid (uniqueProblem 5 0) dupFail_s0_c0Cert emptyState := by native_decide
theorem dupFail_s0_c1_valid :
    Valid (uniqueProblem 5 1) dupFail_s0_c1Cert emptyState := by native_decide
theorem dupFail_s0_c2_valid :
    Valid (uniqueProblem 5 2) dupFail_s0_c2Cert emptyState := by native_decide

theorem dupFail_s1_c0_valid :
    Valid (uniqueProblem 26 0) dupFail_s1_c0Cert emptyState := by native_decide
theorem dupFail_s1_c1_valid :
    Valid (uniqueProblem 26 1) dupFail_s1_c1Cert emptyState := by native_decide
theorem dupFail_s1_c2_valid :
    Valid (uniqueProblem 26 2) dupFail_s1_c2Cert emptyState := by native_decide

theorem dupFail_s2_c0_valid :
    Valid (uniqueProblem 30 0) dupFail_s2_c0Cert emptyState := by native_decide
theorem dupFail_s2_c1_valid :
    Valid (uniqueProblem 30 1) dupFail_s2_c1Cert emptyState := by native_decide
theorem dupFail_s2_c2_valid :
    Valid (uniqueProblem 30 2) dupFail_s2_c2Cert emptyState := by native_decide

theorem dupFail_s3_c0_valid :
    Valid (uniqueProblem 33 0) dupFail_s3_c0Cert emptyState := by native_decide
theorem dupFail_s3_c1_valid :
    Valid (uniqueProblem 33 1) dupFail_s3_c1Cert emptyState := by native_decide
theorem dupFail_s3_c2_valid :
    Valid (uniqueProblem 33 2) dupFail_s3_c2Cert emptyState := by native_decide

theorem dupFail_s4_c0_valid :
    Valid (uniqueProblem 37 0) dupFail_s4_c0Cert emptyState := by native_decide
theorem dupFail_s4_c1_valid :
    Valid (uniqueProblem 37 1) dupFail_s4_c1Cert emptyState := by native_decide
theorem dupFail_s4_c2_valid :
    Valid (uniqueProblem 37 2) dupFail_s4_c2Cert emptyState := by native_decide

theorem dupFail_s5_c0_valid :
    Valid (uniqueProblem 55 0) dupFail_s5_c0Cert emptyState := by native_decide
theorem dupFail_s5_c1_valid :
    Valid (uniqueProblem 55 1) dupFail_s5_c1Cert emptyState := by native_decide
theorem dupFail_s5_c2_valid :
    Valid (uniqueProblem 55 2) dupFail_s5_c2Cert emptyState := by native_decide

/-! ## Replay the three no-missing-colour certificates -/

theorem missing_c0_valid :
    Valid (missingProblem 0) missing_c0Cert emptyState := by native_decide
theorem missing_c1_valid :
    Valid (missingProblem 1) missing_c1Cert emptyState := by native_decide
theorem missing_c2_valid :
    Valid (missingProblem 2) missing_c2Cert emptyState := by native_decide

private theorem unique5 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 5 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s0_c0_valid
  · exact valid_no_colouring dupFail_s0_c1_valid
  · exact valid_no_colouring dupFail_s0_c2_valid

private theorem unique26 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 26 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s1_c0_valid
  · exact valid_no_colouring dupFail_s1_c1_valid
  · exact valid_no_colouring dupFail_s1_c2_valid

private theorem unique30 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 30 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s2_c0_valid
  · exact valid_no_colouring dupFail_s2_c1_valid
  · exact valid_no_colouring dupFail_s2_c2_valid

private theorem unique33 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 33 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s3_c0_valid
  · exact valid_no_colouring dupFail_s3_c1_valid
  · exact valid_no_colouring dupFail_s3_c2_valid

private theorem unique37 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 37 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s4_c0_valid
  · exact valid_no_colouring dupFail_s4_c1_valid
  · exact valid_no_colouring dupFail_s4_c2_valid

private theorem unique55 (k : Fin 3) :
    ¬ exists c, SearchProper (uniqueProblem 55 k) c := by
  fin_cases k
  · exact valid_no_colouring dupFail_s5_c0_valid
  · exact valid_no_colouring dupFail_s5_c1_valid
  · exact valid_no_colouring dupFail_s5_c2_valid

theorem zero_neighbour_cases : forall s : V, adjacent 0 s = true ->
    s = 5 ∨ s = 26 ∨ s = 30 ∨ s = 33 ∨ s = 37 ∨ s = 55 := by
  native_decide

theorem uniqueProblem_uncolourable (s : V) (hs : adjacent 0 s = true)
    (k : Fin 3) : ¬ exists c, SearchProper (uniqueProblem s k) c := by
  rcases zero_neighbour_cases s hs with h | h | h | h | h | h
  · subst s; exact unique5 k
  · subst s; exact unique26 k
  · subst s; exact unique30 k
  · subst s; exact unique33 k
  · subst s; exact unique37 k
  · subst s; exact unique55 k

theorem missingProblem_uncolourable (k : Fin 3) :
    ¬ exists c, SearchProper (missingProblem k) c := by
  fin_cases k
  · exact valid_no_colouring missing_c0_valid
  · exact valid_no_colouring missing_c1_valid
  · exact valid_no_colouring missing_c2_valid

/-! ## Relate list instances back to punctured graph colourings -/

theorem searchProper_missing {c : V -> Fin 3} {k : Fin 3}
    (hp : ProperExcept G 0 c)
    (ha : forall x, adjacent 0 x = true -> c x ≠ k) :
    SearchProper (missingProblem k) c := by
  constructor
  · intro v _hv
    by_cases hn : adjacent 0 v = true
    · simp [missingProblem, hn, ha v hn]
    · have hfalse : adjacent 0 v = false := Bool.eq_false_of_not_eq_true hn
      simp [missingProblem, hfalse]
  · intro u v hu hv huv
    apply hp u v huv
    · simpa [missingProblem, puncturedActive] using hu
    · simpa [missingProblem, puncturedActive] using hv

theorem searchProper_unique {c : V -> Fin 3} {s : V} {k : Fin 3}
    (hp : ProperExcept G 0 c) (hsk : c s = k)
    (hu : forall x, x ≠ s -> adjacent 0 x = true -> c x ≠ k) :
    SearchProper (uniqueProblem s k) c := by
  constructor
  · intro v _hv
    by_cases hvs : v = s
    · subst v
      simp [uniqueProblem, hsk]
    · by_cases hn : adjacent 0 v = true
      · simp [uniqueProblem, hvs, hn, hu v hvs hn]
      · have hfalse : adjacent 0 v = false := Bool.eq_false_of_not_eq_true hn
        simp [uniqueProblem, hvs, hfalse]
  · intro u v hu0 hv0 huv
    apply hp u v huv
    · simpa [uniqueProblem, puncturedActive] using hu0
    · simpa [uniqueProblem, puncturedActive] using hv0

theorem root_two_per_colour : forall (c : V -> Fin 3),
    ProperExcept G 0 c -> forall k : Fin 3,
    exists x y, x ≠ y ∧ adjacent 0 x = true ∧ adjacent 0 y = true ∧
      c x = k ∧ c y = k := by
  intro c hp k
  have hone : exists x, adjacent 0 x = true ∧ c x = k := by
    by_contra hn
    have ha : forall x, adjacent 0 x = true -> c x ≠ k := by
      intro x hx hcx
      exact hn ⟨x, hx, hcx⟩
    exact missingProblem_uncolourable k ⟨c, searchProper_missing hp ha⟩
  obtain ⟨x, hx, hcx⟩ := hone
  have htwo : exists y, y ≠ x ∧ adjacent 0 y = true ∧ c y = k := by
    by_contra hn
    have hu : forall y, y ≠ x -> adjacent 0 y = true -> c y ≠ k := by
      intro y hyx hy hcy
      exact hn ⟨y, hyx, hy, hcy⟩
    exact uniqueProblem_uncolourable x hx k
      ⟨c, searchProper_unique hp hcx hu⟩
  obtain ⟨y, hyx, hy, hcy⟩ := htwo
  exact ⟨x, y, Ne.symm hyx, hx, hy, hcx, hcy⟩

/-! ## Transport the root result by concrete Cayley translations -/

theorem candidate_balanced_punctures : TwoPerColourAtPunctures G (Fin 3) := by
  intro r c hp k
  let d : V -> Fin 3 := fun z => c (unshift r z)
  have hdp : ProperExcept G 0 d := by
    intro u v huv hu0 hv0
    apply hp (unshift r u) (unshift r v)
    · change adjacent (unshift r u) (unshift r v) = true
      rw [unshift_preserves_adjacency r u v]
      simpa [G] using huv
    · intro heq
      have heq' : unshift r u = unshift r 0 := by
        simpa [unshift_zero] using heq
      exact hu0 (unshift_injective r heq')
    · intro heq
      have heq' : unshift r v = unshift r 0 := by
        simpa [unshift_zero] using heq
      exact hv0 (unshift_injective r heq')
  obtain ⟨x, y, hxy, hx, hy, hcx, hcy⟩ := root_two_per_colour d hdp k
  refine ⟨unshift r x, unshift r y, ?_, ?_, ?_, hcx, hcy⟩
  · exact fun h => hxy (unshift_injective r h)
  · have hpres := unshift_preserves_adjacency r 0 x
    have hpres' : adjacent r (unshift r x) = adjacent 0 x := by
      simpa [unshift_zero] using hpres
    change adjacent r (unshift r x) = true
    rw [hpres']
    exact hx
  · have hpres := unshift_preserves_adjacency r 0 y
    have hpres' : adjacent r (unshift r y) = adjacent 0 y := by
      simpa [unshift_zero] using hpres
    change adjacent r (unshift r y) = true
    rw [hpres']
    exact hy

/-! The customary numerical form: the neighbour-colour profile is 2+2+2. -/

def neighbours (r : V) : Finset V :=
  Finset.univ.filter (fun x => adjacent r x = true)

def neighbourColourCount (r : V) (c : V -> Fin 3) (k : Fin 3) : Nat :=
  ((neighbours r).filter (fun x => c x = k)).card

theorem every_vertex_has_degree_six : forall r : V, (neighbours r).card = 6 := by
  native_decide

private theorem two_le_neighbourColourCount (r : V) (c : V -> Fin 3)
    (hp : ProperExcept G r c) (k : Fin 3) :
    2 ≤ neighbourColourCount r c k := by
  obtain ⟨x, y, hxy, hx, hy, hcx, hcy⟩ :=
    candidate_balanced_punctures r c hp k
  have hsubset : ({x, y} : Finset V) ⊆
      (neighbours r).filter (fun z => c z = k) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzx | hzy
    · subst z
      have hx' : adjacent r x = true := by simpa [G] using hx
      simp [neighbours, hx', hcx]
    · subst z
      have hy' : adjacent r y = true := by simpa [G] using hy
      simp [neighbours, hy', hcy]
  calc
    2 = ({x, y} : Finset V).card := by simp [hxy]
    _ ≤ ((neighbours r).filter (fun z => c z = k)).card :=
      Finset.card_le_card hsubset

theorem exact_two_two_two_profile (r : V) (c : V -> Fin 3)
    (hp : ProperExcept G r c) : forall k : Fin 3,
    neighbourColourCount r c k = 2 := by
  let A := (neighbours r).filter (fun x => c x = (0 : Fin 3))
  let B := (neighbours r).filter (fun x => c x = (1 : Fin 3))
  let C := (neighbours r).filter (fun x => c x = (2 : Fin 3))
  have hcover : (A ∪ B) ∪ C = neighbours r := by
    ext x
    by_cases hcx0 : c x = 0
    · simp [A, B, C, hcx0]
    · by_cases hcx1 : c x = 1
      · simp [A, B, C, hcx0, hcx1]
      · have hcx2 : c x = 2 := by omega
        simp [A, B, C, hcx0, hcx1, hcx2]
  have hdAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxB
    simp only [A, Finset.mem_filter] at hxA
    simp only [B, Finset.mem_filter] at hxB
    exact (by decide : (0 : Fin 3) ≠ 1) (hxA.2.symm.trans hxB.2)
  have hdAC : Disjoint A C := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxC
    simp only [A, Finset.mem_filter] at hxA
    simp only [C, Finset.mem_filter] at hxC
    exact (by decide : (0 : Fin 3) ≠ 2) (hxA.2.symm.trans hxC.2)
  have hdBC : Disjoint B C := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxB hxC
    simp only [B, Finset.mem_filter] at hxB
    simp only [C, Finset.mem_filter] at hxC
    exact (by decide : (1 : Fin 3) ≠ 2) (hxB.2.symm.trans hxC.2)
  have hdABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxAB hxC
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact Finset.disjoint_left.mp hdAC hxA hxC
    · exact Finset.disjoint_left.mp hdBC hxB hxC
  have hsum : A.card + B.card + C.card = 6 := by
    calc
      A.card + B.card + C.card = (A ∪ B).card + C.card := by
        rw [Finset.card_union_of_disjoint hdAB]
      _ = ((A ∪ B) ∪ C).card := by
        rw [Finset.card_union_of_disjoint hdABC]
      _ = (neighbours r).card := by rw [hcover]
      _ = 6 := every_vertex_has_degree_six r
  have hA : 2 ≤ A.card := by
    simpa [A, neighbourColourCount] using
      two_le_neighbourColourCount r c hp (0 : Fin 3)
  have hB : 2 ≤ B.card := by
    simpa [B, neighbourColourCount] using
      two_le_neighbourColourCount r c hp (1 : Fin 3)
  have hC : 2 ≤ C.card := by
    simpa [C, neighbourColourCount] using
      two_le_neighbourColourCount r c hp (2 : Fin 3)
  have hAe : A.card = 2 := by omega
  have hBe : B.card = 2 := by omega
  have hCe : C.card = 2 := by omega
  intro k
  fin_cases k
  · simpa [A, neighbourColourCount] using hAe
  · simpa [B, neighbourColourCount] using hBe
  · simpa [C, neighbourColourCount] using hCe

theorem order60_solution : FourVertexCritical G ∧ EdgeImmuneAtFour G :=
  balanced_puncture_decoupling G graph_is_four_colourable
    every_vertex_deletion_is_three_colourable candidate_balanced_punctures

theorem order60_four_vertex_critical : FourVertexCritical G :=
  order60_solution.1

theorem order60_has_no_critical_edges : EdgeImmuneAtFour G :=
  order60_solution.2

end Dirac60
