import QuaternaryQuadraticForms.QuadricCountingTheorem
import QuaternaryQuadraticForms.CompleteSumAlgebra
import Mathlib.Data.Rat.Lemmas

/-! # Inverse-radius counting on the actual dual cone -/

noncomputable section
namespace QuaternaryQuadraticForms

/-- The nonzero lattice frequencies up to U on the dual quadric. -/
def dualConeFrequencies (A : Matrix (Fin 4) (Fin 4) ℤ) (U : ℝ) : Finset (Fin 4 → ℤ) :=
  (integerEuclideanBall U).filter (fun u => u ≠ 0 ∧ dotProduct u (A.adjugate.mulVec u) = 0)

private theorem inverseRadius_quadratic {α : Type*} (s : Finset α) (r : α → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (U : ℝ) (hU : 1 ≤ U) (hr : ∀ a ∈ s, 1 ≤ r a)
    (hmax : ∀ a ∈ s, r a ≤ U)
    (hcount : ∀ T : ℝ, 1 ≤ T → T ≤ U → ((s.filter (fun a => r a ≤ T)).card : ℝ) ≤ D*T^2) :
    ∑ a ∈ s, (r a)⁻¹ ≤ 4*D*U := by
  classical
  induction s using Finset.strongInductionOn generalizing U with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp only [Finset.sum_empty]; positivity
    obtain ⟨a,ha,ham⟩ := s.exists_max_image r hs
    let M := r a
    have hM : 1 ≤ M := hr a ha
    have hpos : 0 < M := by linarith
    let t := s.filter (fun x => r x ≤ M/2)
    have ht : t ⊆ s := Finset.filter_subset _ _
    have hlt : t ⊂ s := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨ht, ?_⟩
      intro h
      have hat : a ∈ t := h.symm ▸ ha
      have hh : M ≤ M/2 := (Finset.mem_filter.mp hat).2
      linarith
    have hcard : (s.card:ℝ) ≤ D*M^2 := by
      have hall : s.filter (fun x => r x ≤ M) = s := Finset.filter_eq_self.mpr ham
      simpa only [hall] using hcount M hM (hmax a ha)
    have houter : ∑ x ∈ s \ t, (r x)⁻¹ ≤ 2*D*M := by
      calc
        _ ≤ ∑ _ ∈ s \ t, 2/M := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨hxs,hxt⟩ := Finset.mem_sdiff.mp hx
          have h : M/2 < r x := lt_of_not_ge (fun hh => hxt (Finset.mem_filter.mpr ⟨hxs,hh⟩))
          rw [← one_div]
          apply (div_le_div_iff₀ (zero_lt_one.trans_le (hr x hxs)) hpos).2
          linarith
        _ = ((s \ t).card:ℝ)*(2/M) := by simp
        _ ≤ (s.card:ℝ)*(2/M) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) (by positivity)
        _ ≤ (D*M^2)*(2/M) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp
    have hinner : ∑ x ∈ t, (r x)⁻¹ ≤ 2*D*M := by
      by_cases hh : 1 ≤ M/2
      · have hhalf := ih t hlt (M/2) hh (fun x hx => hr x (ht hx))
          (fun x hx => (Finset.mem_filter.mp hx).2) (fun T hT hTM => by
            refine le_trans ?_ (hcount T hT (hTM.trans (by linarith [hmax a ha] : M/2 ≤ U)))
            exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ ht))
        linarith
      · have hempty : t = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx =>
          hh ((hr x (ht hx)).trans (Finset.mem_filter.mp hx).2))
        rw [hempty, Finset.sum_empty]; positivity
    have heq := Finset.sum_sdiff_eq_sub (f := fun x => (r x)⁻¹) ht
    exact (show ∑ x ∈ s, (r x)⁻¹ ≤ 4*D*M by linarith).trans
      (mul_le_mul_of_nonneg_left (hmax a ha) (by positivity))

/-- The bound in equation conecount for the adjugate of the source matrix.
The constant depends only on the integral form and the positive exponent. -/
theorem source_dual_cone_count (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hd : A.det ≠ 0) (hns : ¬ IsSquare A.det) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ∑ u ∈ dualConeFrequencies A U, (integerEuclideanNorm u)⁻¹ ≤ C*U^(1+ε) := by
  let S := A.adjugate.map (Int.castRingHom ℚ)
  have hS : S.transpose = S := by
    change (A.adjugate.transpose.map (Int.castRingHom ℚ)) = _
    rw [Matrix.adjugate_transpose, hA]
  have hdet : S.det = (A.det:ℚ)^3 := by
    calc
      _ = ((A.adjugate.det : ℤ):ℚ) := ((Int.castRingHom ℚ).map_det _).symm
      _ = _ := by simp [Matrix.det_adjugate]
  have hq : (A.det:ℚ) ≠ 0 := by exact_mod_cast hd
  have hnot : ¬ IsSquare S.det := by
    rw [hdet]
    rintro ⟨z,hz⟩
    apply hns
    apply Rat.isSquare_intCast_iff.mp
    refine ⟨z/(A.det:ℚ), ?_⟩
    field_simp
    linear_combination hz
  obtain ⟨K,hK,hcount⟩ := rationalQuadric_euclidean_bound S hS (by rw [hdet]; positivity) hnot ε hε
  refine ⟨4*K, by positivity, ?_⟩
  intro U hU
  have hpos : 0 < U := zero_lt_one.trans_le hU
  let s := dualConeFrequencies A U
  have hsub (T : ℝ) : s.filter (fun u => integerEuclideanNorm u ≤ T) ⊆ integerQuadricZeros S T := by
    intro x hx
    obtain ⟨hx,hT⟩ := Finset.mem_filter.mp hx
    obtain ⟨_,_,hz⟩ := Finset.mem_filter.mp hx
    apply (mem_integerQuadricZeros S T x).2 ⟨hT, ?_⟩
    apply (matrixQuadraticValue_map (Int.castRingHom ℚ) A.adjugate x).symm.trans
    change (dotProduct x (A.adjugate.mulVec x) : ℤ) = 0 at hz
    rw [hz, map_zero]
  calc
    _ ≤ 4*(K*U^ε)*U := by
      apply inverseRadius_quadratic s integerEuclideanNorm _ (by positivity) U hU
      · intro x hx; exact one_le_integerEuclideanNorm _ (Finset.mem_filter.mp hx).2.1
      · intro x hx; exact (mem_integerEuclideanBall U x).mp (Finset.mem_filter.mp hx).1
      · intro T hT hTU
        have ht : 0 < T := zero_lt_one.trans_le hT
        calc
          _ ≤ ((integerQuadricZeros S T).card:ℝ) := by exact_mod_cast Finset.card_le_card (hsub T)
          _ ≤ K*T^(2+ε) := hcount _ hT
          _ = K*T^ε*T^2 := by rw [Real.rpow_add ht, Real.rpow_two]; ring
          _ ≤ _ := by gcongr
    _ = _ := by rw [Real.rpow_add hpos, Real.rpow_one]; ring

end QuaternaryQuadraticForms
