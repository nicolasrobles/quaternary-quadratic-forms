import QuaternaryQuadraticForms.ModulusNormSum
import QuaternaryQuadraticForms.FactorizationSumBound
import QuaternaryQuadraticForms.MixedSumGcdBound
import QuaternaryQuadraticForms.PrimeSupportCount
import QuaternaryQuadraticForms.GcdHarmonicBound

/-!
# The finite modulus sum and its divisor-logarithm bound

Every modulus in the actual gcd-restricted sum is assigned its proved
bad-prime/good-prime factorization. Multiplication recovers the modulus,
so these pairs inject into a finite rectangle. The first coordinate is
counted by its prime support and the second by the gcd harmonic estimate.
The divisibility support is inherited from the actual complete sums.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual modulus sum vanishes outside the source's integral
divisibility condition, for every real cutoff. -/
theorem modulusNormSum_eq_zero_of_not_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d : ℕ) [NeZero q] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ) (X : ℝ)
    (hnot : ¬(d : ℤ) ∣ dotProduct u (A.adjugate.mulVec u)) :
    modulusNormSum ξ q d A u X = 0 := by
  apply modulusNormSum_eq_zero_of_vanishing ξ q d A u X
  intro c hc
  have hmem := (mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc
  letI : NeZero c := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hmem.1)⟩
  have hgd : q.gcd c = d := (Nat.gcd_comm q c).trans hmem.2.2
  apply mixedCompleteSum_eq_zero_of_gcd_not_dvd ξ q c hq A hA hqA hξ u
  simpa only [hgd] using hnot

private theorem modulusNormSum_le_primeSupport_card_mul_gcd_sum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e]
    (hq : Squarefree q) (hqde : q = d * e)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (u : Fin 4 → ℤ) (X : ℝ) :
    modulusNormSum ξ q d A u X ≤
      ((primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊).card : ℝ) *
        (4 * Real.sqrt (A.det.natAbs : ℝ) *
          ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2) *
        ∑ g ∈ Finset.Icc 1 ⌊X⌋₊,
          (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ) := by
  classical
  have hsplits (c : ℕ) : ∃ b g : ℕ, c ≠ 0 →
      b ≠ 0 ∧ g ≠ 0 ∧ c = b * g ∧ b.Coprime g ∧
        g.Coprime (quadraticBadPrimeModulus A) ∧
        (∀ p : ℕ, p.Prime → p ∣ b → p ∣ quadraticBadPrimeModulus A) := by
    by_cases hc : c = 0
    · exact ⟨1, 1, fun h => (h hc).elim⟩
    · obtain ⟨b, g, hs⟩ := exists_modulus_prime_split c (quadraticBadPrimeModulus A) hc
      exact ⟨b, g, fun _ => hs⟩
  choose b g hsplit using hsplits
  refine sum_le_product_of_factorization
    (gcdModuliUpTo q d ⌊X⌋₊)
    (primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊)
    (Finset.Icc 1 ⌊X⌋₊) (fun c => (b c, g c))
    (fun c => normalizedMixedCompleteSum ξ q c A u)
    (fun g => (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ))
    (4 * Real.sqrt (A.det.natAbs : ℝ) *
      ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    obtain ⟨hcpos, hcT, _⟩ := (mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc
    have hcpos' : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hcpos
    obtain ⟨hb, hg, hcg, _, _, hbA⟩ := hsplit c hcpos'.ne'
    have hbdvd : b c ∣ c := ⟨g c, hcg⟩
    have hgdvd : g c ∣ c := ⟨b c, by simpa only [Nat.mul_comm] using hcg⟩
    apply Finset.mem_product.mpr
    exact ⟨(mem_primeSupportModuliUpTo _ _ _).mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hb, (Nat.le_of_dvd hcpos' hbdvd).trans hcT, hbA⟩,
      Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hg, (Nat.le_of_dvd hcpos' hgdvd).trans hcT⟩⟩
  · intro c hc
    have hcpos := ((mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc).1
    exact (hsplit c (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hcpos))).2.2.1
  · intro c hc
    have hmem := (mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc
    have hcnz : c ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hmem.1)
    obtain ⟨hb, hg, hcg, hbg, hgA, hbA⟩ := hsplit c hcnz
    letI : NeZero c := ⟨hcnz⟩
    letI : NeZero (b c) := ⟨hb⟩
    letI : NeZero (g c) := ⟨hg⟩
    have hgd : q.gcd c = d := (Nat.gcd_comm q c).trans hmem.2.2
    have hqe : q / d = e := by
      rw [hqde]
      exact Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero (NeZero.ne d))
    dsimp only
    rw [normalizedMixedCompleteSum_of_neZero]
    have hbound := mixedCompleteSum_div_cube_le_gcd_of_prime_split
      ξ q c (b c) (g c) hq A hA hdet hqA hcg hbg hgA hbA hξ hξnorm u
    simpa only [hgd, hqe, mul_div_assoc] using hbound
  · positivity
  · intro g _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The actual finite modulus sum has a uniform explicit bound with
one divisor-count factor and the bad-prime logarithmic exponent. -/
theorem modulusNormSum_le_divisor_log
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e]
    (hq : Squarefree q) (hqde : q = d * e)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0)
    (X : ℝ) (hX : 1 ≤ X) :
    modulusNormSum ξ q d A u X ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) *
        (1 + (Real.log 2)⁻¹) ^ (quadraticBadPrimeModulus A).primeFactors.card *
        ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2 *
        ((dotProduct u (A.adjugate.mulVec u)).natAbs.divisors.card : ℝ) *
        (1 + Real.log X) ^ ((quadraticBadPrimeModulus A).primeFactors.card + 1) := by
  have hcard := primeSupportModuliUpTo_card_le_log_normalized
    (quadraticBadPrimeModulus A) (quadraticBadPrimeModulus_ne_zero A hdet) X hX
  have hsum := sum_gcd_div_le_divisor_card_mul_log
    (dotProduct u (A.adjugate.mulVec u)).natAbs (Int.natAbs_ne_zero.mpr hu) X hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlog2 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  have hK : 0 ≤ 4 * Real.sqrt (A.det.natAbs : ℝ) *
      ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2 := by positivity
  have hsum0 : 0 ≤ ∑ g ∈ Finset.Icc 1 ⌊X⌋₊,
      (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ) :=
    Finset.sum_nonneg (fun g _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ ((primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊).card : ℝ) *
        (4 * Real.sqrt (A.det.natAbs : ℝ) *
          ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2) *
        ∑ g ∈ Finset.Icc 1 ⌊X⌋₊,
          (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ) :=
      modulusNormSum_le_primeSupport_card_mul_gcd_sum
        ξ q d e hq hqde A hA hdet hqA hξ hξnorm u X
    _ ≤ ((1 + (Real.log 2)⁻¹) ^ (quadraticBadPrimeModulus A).primeFactors.card *
        (1 + Real.log X) ^ (quadraticBadPrimeModulus A).primeFactors.card) *
        (4 * Real.sqrt (A.det.natAbs : ℝ) *
          ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2) *
        ∑ g ∈ Finset.Icc 1 ⌊X⌋₊,
          (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hK) hsum0
    _ ≤ ((1 + (Real.log 2)⁻¹) ^ (quadraticBadPrimeModulus A).primeFactors.card *
        (1 + Real.log X) ^ (quadraticBadPrimeModulus A).primeFactors.card) *
        (4 * Real.sqrt (A.det.natAbs : ℝ) *
          ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2) *
        (((dotProduct u (A.adjugate.mulVec u)).natAbs.divisors.card : ℝ) *
          (1 + Real.log X)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [pow_succ]; ring

end QuaternaryQuadraticForms
