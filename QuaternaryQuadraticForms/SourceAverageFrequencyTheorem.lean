import QuaternaryQuadraticForms.SourceFourierSums
import QuaternaryQuadraticForms.SourceExceptionalPolynomials
import QuaternaryQuadraticForms.FourierProductBound
import QuaternaryQuadraticForms.AverageFrequencyBound

/-!
# The complete source estimate of Lemma 3.11

The final theorem bounds the actual Fourier sums formed from the original
functions supplied only at good primes. The local stratified estimate is
the explicit hypothesis of Section 3. Its prime product and divisor
expansion are proved, and the coefficient-uniform weighted congruence
estimate discharges every counting step. The constant is selected before
all matrix, polynomial, weight, modulus and radius data.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Lemma 3.11 for a natural degree bound, with the literal source
Fourier sums and the exact squarefree factorization `q = q₁*q₂`. -/
theorem source_average_frequency_natDegree (E : ℕ) (hE : 1 ≤ E)
    (K : ℝ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), 1 ≤ N → primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), D p hp hpN ≠ 0) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), (D p hp hpN).totalDegree ≤ E) →
      ∀ (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
          ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N) (u : Fin 4 → ℤ),
          ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
              (hp.coprime_iff_not_dvd.mpr hpN) A u‖ ≤
            K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
              (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p hp hpN) = 0
                then 1 else 0))) →
      ∀ (q q₁ q₂ : ℕ) [NeZero q] [NeZero q₁] [NeZero q₂],
        Squarefree q → ∀ (hqeq : q = q₁ * q₂) (hqN : q.Coprime N),
      ∀ (U : ℝ), 1 ≤ U →
        (∑ u ∈ divisibleEuclideanBall A q₁ U,
          ‖sourceConstrainedFourierSum N ξ q₂
              (hqN.of_dvd_left (by rw [hqeq]; exact dvd_mul_left q₂ q₁)) A u‖ /
            integerEuclideanNorm u) ≤
          C * (q : ℝ) ^ ε * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
            (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := averageFrequency_bound E hE K hK ε hε
  refine ⟨C, hC, ?_⟩
  intro A hA hdet N _hN hrad D hD hdeg ξ hξ hlocal q q₁ q₂ _ _ _
    hsq hqeq hqN U hU
  have hsqprod : Squarefree (q₁ * q₂) := hqeq ▸ hsq
  obtain ⟨hcop, hsq₁, hsq₂⟩ := Nat.squarefree_mul_iff.mp hsqprod
  have hcopN : (q₁ * q₂).Coprime N := hqeq ▸ hqN
  have hq₂N : q₂.Coprime N := hcopN.of_dvd_left (dvd_mul_left q₂ q₁)
  have hmajor (u : Fin 4 → ℤ) :
      ‖constrainedFourierSum (extendPrimeWeights N ξ) q₂ A u‖ ≤
        K ^ q₂.primeFactors.card * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
          ∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
            exceptionalIndicator (extendExceptionalPolynomials N D) h u := by
    apply constrainedFourierSum_norm_le_divisors (extendPrimeWeights N ξ)
      (extendExceptionalPolynomials N D) q₂ A u K hsq₂
      (primeWeightsInvariant_extend N q₂ ξ hq₂N hξ)
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    letI : NeZero p := ⟨hpp.ne_zero⟩
    have hpN : ¬p ∣ N := hpp.coprime_iff_not_dvd.mp
      (hq₂N.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    rw [constrainedFourierSum_extend_eq_source N ξ p
      (hpp.coprime_iff_not_dvd.mpr hpN) A u,
      extendExceptionalPolynomials_apply N D p hpp hpN]
    exact hlocal p hpp hpN u
  have hb := hbound A hA hdet N hrad (extendExceptionalPolynomials N D)
    (extendExceptionalPolynomials_ne_zero N D hD)
    (extendExceptionalPolynomials_totalDegree_le N E D hdeg)
    q₁ q₂ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁))
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)) hsq₁ hsq₂ hcop hcopN U hU
    (fun u => ‖constrainedFourierSum (extendPrimeWeights N ξ) q₂ A u‖) hmajor
  simpa only [hqeq, constrainedFourierSum_extend_eq_source N ξ q₂ hq₂N] using hb

/-- Complete Lemma 3.11, allowing a real degree bound as in the source.
One positive constant depends only on `E`, `K`, and `ε`; all actual source
data and every positive squarefree factorization are quantified afterwards. -/
theorem source_average_frequency_bound (E K ε : ℝ)
    (hE : 1 ≤ E) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), 1 ≤ N → primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), D p hp hpN ≠ 0) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ((D p hp hpN).totalDegree : ℝ) ≤ E) →
      ∀ (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
          ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N) (u : Fin 4 → ℤ),
          ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
              (hp.coprime_iff_not_dvd.mpr hpN) A u‖ ≤
            K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
              (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p hp hpN) = 0
                then 1 else 0))) →
      ∀ (q q₁ q₂ : ℕ) [NeZero q] [NeZero q₁] [NeZero q₂],
        Squarefree q → ∀ (hqeq : q = q₁ * q₂) (hqN : q.Coprime N),
      ∀ (U : ℝ), 1 ≤ U →
        (∑ u ∈ divisibleEuclideanBall A q₁ U,
          ‖sourceConstrainedFourierSum N ξ q₂
              (hqN.of_dvd_left (by rw [hqeq]; exact dvd_mul_left q₂ q₁)) A u‖ /
            integerEuclideanNorm u) ≤
          C * (q : ℝ) ^ ε * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
            (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
  have hceil : 1 ≤ Nat.ceil E := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hE)
  obtain ⟨C, hC, hbound⟩ := source_average_frequency_natDegree (Nat.ceil E) hceil K hK ε hε
  refine ⟨C, hC, ?_⟩
  intro A hA hdet N hN hrad D hD hdeg
  have hnat : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N),
      (D p hp hpN).totalDegree ≤ Nat.ceil E := by
    intro p hp hpN
    exact_mod_cast (hdeg p hp hpN).trans (Nat.le_ceil E)
  exact hbound A hA hdet N hN hrad D hD hnat

end QuaternaryQuadraticForms
