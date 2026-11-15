import QuaternaryQuadraticForms.SingularSeriesDefinitions
import QuaternaryQuadraticForms.OrderedSeriesTail
import QuaternaryQuadraticForms.ConeModulusTheorem

/-!
# Ordered convergence, boundary continuity, and the uniform singular-series tail

The coefficient cancellation is the proved bound for the actual complete sums
in Lemma 3.7.  The order of the moduli is retained at shift zero.
-/

noncomputable section

open Finset Filter MeasureTheory Topology

namespace QuaternaryQuadraticForms

theorem singularSeriesPartialSum_eq_orderedDirichletPartial
    (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) (z X : ℝ) :
    singularSeriesPartialSum q A z X =
      orderedDirichletPartial (coprimeCompleteSumValue q A) (4 + z) X := by
  unfold singularSeriesPartialSum orderedDirichletPartial
  rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊X⌋₊),
    sum_insert (by aesop), coprimeCompleteSumValue_zero, mul_zero, zero_add, zero_add]
  apply sum_congr rfl
  intro c _
  rw [singularSeriesTerm, Complex.ofReal_cpow (Nat.cast_nonneg c),
    Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
  exact mul_comm _ _

/-- Lemma 3.7 in the coefficient normalization needed for Abel summation. -/
theorem exists_coprimeCompleteSumValue_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q],
      q.Coprime (quadraticBadPrimeModulus A) → ∀ (X : ℝ), 1 ≤ X →
        ‖orderedCoeffSum (coprimeCompleteSumValue q A) X‖ ≤
          (C * (q : ℝ) ^ η) * X ^ (3 + η) := by
  obtain ⟨C, hC, hb⟩ := unweightedModulusSum_le_rpow A hA hdet hns η hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq X hX
  rw [orderedCoeffSum_eq_Icc_one _ (coprimeCompleteSumValue_zero q A),
    sum_coprimeCompleteSumValue]
  calc
    _ ≤ C * X ^ 3 * (X * (q : ℝ)) ^ η :=
      hb q 1 q (by simp) hq 0 (by simp) X hX
    _ = _ := by
      rw [Real.mul_rpow (zero_le_one.trans hX) (Nat.cast_nonneg q),
        Real.rpow_add (zero_lt_one.trans_le hX), Real.rpow_ofNat]
      ring

/-- A cancellation hypothesis identifies the ordered value with its Abel integral. -/
theorem singularSeriesValue_eq_orderedDirichletValue_of_bound
    (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) {K η z : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hz : 0 ≤ z)
    (hbound : ∀ v : ℝ, 1 ≤ v →
      ‖orderedCoeffSum (coprimeCompleteSumValue q A) v‖ ≤ K * v ^ (3 + η)) :
    singularSeriesValue q A z =
      orderedDirichletValue (coprimeCompleteSumValue q A) (4 + z) := by
  have h := tendsto_orderedDirichletPartial (coprimeCompleteSumValue q A)
    (coprimeCompleteSumValue_zero q A) hηpos hη (by linarith : 4 ≤ 4 + z) hbound
  have h' : Tendsto (singularSeriesPartialSum q A z) atTop
      (𝓝 (orderedDirichletValue (coprimeCompleteSumValue q A) (4 + z))) := by
    simpa only [funext (singularSeriesPartialSum_eq_orderedDirichletPartial q A z)] using h
  exact h'.limUnder_eq

/-- The actual shifted ordered series converges, including the boundary shift zero. -/
theorem tendsto_singularSeriesPartialSum
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A))
    (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (singularSeriesPartialSum q A z) atTop (𝓝 (singularSeriesValue q A z)) := by
  obtain ⟨C, _hC, hb⟩ := exists_coprimeCompleteSumValue_bound A hA hdet hns (1 / 2) (by norm_num)
  rw [singularSeriesValue_eq_orderedDirichletValue_of_bound q A
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hz (hb q hq)]
  simpa only [funext (singularSeriesPartialSum_eq_orderedDirichletPartial q A z)] using
    tendsto_orderedDirichletPartial (coprimeCompleteSumValue q A)
      (coprimeCompleteSumValue_zero q A) (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
      (by linarith : 4 ≤ 4 + z) (hb q hq)

/-- Right continuity of the actual ordered series at its boundary. -/
theorem continuousWithinAt_singularSeriesValue_zero
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A)) :
    ContinuousWithinAt (singularSeriesValue q A) (Set.Ici 0) 0 := by
  obtain ⟨C, hC, hb⟩ := exists_coprimeCompleteSumValue_bound A hA hdet hns (1 / 2) (by norm_num)
  have hK : 0 ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hcont := continuousWithinAt_orderedDirichletValue_four
    (coprimeCompleteSumValue q A) hK (le_refl (1 / 2 : ℝ)) (hb q hq)
  have hshift : ContinuousWithinAt
      (fun z : ℝ ↦ orderedDirichletValue (coprimeCompleteSumValue q A) (4 + z))
      (Set.Ici 0) 0 := by
    have hmaps : Set.MapsTo (fun z : ℝ ↦ 4 + z) (Set.Ici 0) (Set.Ici 4) := by
      intro z hz
      change 4 ≤ 4 + z
      linarith [show 0 ≤ z from hz]
    exact hcont.comp_of_eq (continuousWithinAt_const.add continuousWithinAt_id) hmaps (by norm_num)
  apply hshift.congr_of_mem _ (show (0 : ℝ) ∈ Set.Ici 0 by simp)
  intro z hz
  exact singularSeriesValue_eq_orderedDirichletValue_of_bound q A
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hz (hb q hq)

/-- The positive tail constant is chosen before the modulus, shift, and real cutoff. -/
theorem singularSeries_uniform_tail
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q],
      q.Coprime (quadraticBadPrimeModulus A) →
      ∀ (z : ℝ), 0 ≤ z → ∀ (X : ℝ), 1 ≤ X →
        ‖singularSeriesValue q A z - singularSeriesPartialSum q A z X‖ ≤
          C * (q : ℝ) ^ ε * X ^ (-1 + ε) := by
  let η : ℝ := min ε (1 / 2)
  have hηpos : 0 < η := lt_min hε (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  obtain ⟨K, hK, hb⟩ := exists_coprimeCompleteSumValue_bound A hA hdet hns η hηpos
  refine ⟨9 * K, by positivity, ?_⟩
  intro q _ hq z hz X hX
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rw [singularSeriesValue_eq_orderedDirichletValue_of_bound q A hηpos hηhalf hz (hb q hq),
    singularSeriesPartialSum_eq_orderedDirichletPartial]
  calc
    _ ≤ 9 * (K * (q : ℝ) ^ η) * X ^ (-1 + η) :=
      norm_orderedDirichletValue_sub_partial_le (coprimeCompleteSumValue q A)
        (coprimeCompleteSumValue_zero q A)
        (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)) hηhalf
        (by linarith : 4 ≤ 4 + z) (hb q hq) hX
    _ ≤ (9 * K) * (q : ℝ) ^ ε * X ^ (-1 + ε) := by
      rw [← mul_assoc]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hqone hηε) (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      · exact Real.rpow_nonneg (zero_le_one.trans hX) _
      · positivity

end QuaternaryQuadraticForms
