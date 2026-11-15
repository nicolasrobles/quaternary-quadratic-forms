import QuaternaryQuadraticForms.CongruenceBoxTheorem
import QuaternaryQuadraticForms.ExceptionalDivisorSum
import QuaternaryQuadraticForms.PrimeFactorEpsilon
import QuaternaryQuadraticForms.DivisorPowerBound
import Mathlib.Tactic.GCongr

/-!
# The exceptional-frequency average from the pointwise product bound

This module combines the actual Euclidean congruence sums of Lemma 3.10
with the divisor majorant supplied by the Fourier-product expansion.  Its
constant is chosen before the matrix, the polynomial family, the moduli,
the radius and the function being bounded.  The three small-power factors
use one third of the prescribed exponent each.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The full coefficient-uniform average follows from the pointwise
divisor majorant.  The source wrapper supplies the actual Fourier sums
and proves this majorant from their CRT product and local bounds. -/
theorem averageFrequency_bound (E : ℕ) (hE : 1 ≤ E)
    (K : ℝ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p, p.Prime → ¬p ∣ N → D p ≠ 0) →
        (∀ p, p.Prime → ¬p ∣ N → (D p).totalDegree ≤ E) →
      ∀ (q₁ q₂ : ℕ), 1 ≤ q₁ → 1 ≤ q₂ → Squarefree q₁ → Squarefree q₂ →
        q₁.Coprime q₂ → (q₁ * q₂).Coprime N →
      ∀ (U : ℝ), 1 ≤ U →
      ∀ (f : (Fin 4 → ℤ) → ℝ),
        (∀ u, f u ≤ K ^ q₂.primeFactors.card * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
          ∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u) →
        (∑ u ∈ divisibleEuclideanBall A q₁ U, f u / integerEuclideanNorm u) ≤
          C * ((q₁ * q₂ : ℕ) : ℝ) ^ ε * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
            (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
  classical
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B, hB, hbox⟩ := congruenceBox_bounds E hE η hη
  obtain ⟨C₁, hC₁, hprime⟩ := primeFactor_pow_le_rpow K hK η hη
  obtain ⟨C₂, hC₂, hdivisor⟩ := divisors_card_le_rpow η hη
  refine ⟨B * C₁ * C₂, by positivity, ?_⟩
  intro A hA hdet N hrad D hD hdeg q₁ q₂ hq₁ hq₂ hsq₁ hsq₂ hcop hcopN U hU f hmajor
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hq₂pos : 0 < q₂ := by omega
  have hq₂le : q₂ ≤ q₁ * q₂ := by nlinarith
  have hqpos : (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (show 0 < q₁ by omega) hq₂pos
  have hq₂pow : (q₂ : ℝ) ^ η ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ η :=
    Real.rpow_le_rpow (Nat.cast_nonneg q₂) (by exact_mod_cast hq₂le) hη.le
  have hprime' : K ^ q₂.primeFactors.card ≤ C₁ * ((q₁ * q₂ : ℕ) : ℝ) ^ η :=
    (hprime q₂ hq₂ hsq₂).trans (mul_le_mul_of_nonneg_left hq₂pow hC₁.le)
  have hdivisor' : (q₂.divisors.card : ℝ) ≤ C₂ * ((q₁ * q₂ : ℕ) : ℝ) ^ η :=
    (hdivisor q₂ hq₂pos).trans (mul_le_mul_of_nonneg_left hq₂pow hC₂.le)
  have hweighted (h : ℕ) (hh : h ∈ q₂.divisors) :
      weightedCongruenceEuclideanSum A D q₁ h U ≤
        B * ((q₁ * h : ℕ) : ℝ) ^ η * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2) := by
    have hdvd : h ∣ q₂ := Nat.dvd_of_mem_divisors hh
    exact (hbox A hA hdet N hrad D hD hdeg q₁ h hq₁
      (Nat.pos_of_mem_divisors hh) hsq₁ (hsq₂.squarefree_of_dvd hdvd)
      (hcop.of_dvd_right hdvd)
      (hcopN.of_dvd_left (Nat.mul_dvd_mul_left q₁ hdvd)) U hU).2
  have hsum :
      (∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
        weightedCongruenceEuclideanSum A D q₁ h U) ≤
      B * ((q₁ * q₂ : ℕ) : ℝ) ^ η * (q₂.divisors.card : ℝ) *
        (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
    calc
      _ ≤ ∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
          (B * ((q₁ * h : ℕ) : ℝ) ^ η *
            (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2)) := by
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_left (hweighted h hh)
          (Real.rpow_nonneg (Nat.cast_nonneg h) _)
      _ = B * ∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
          (((q₁ * h : ℕ) : ℝ) ^ η *
            (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _hh
        ring
      _ ≤ B * (((q₁ * q₂ : ℕ) : ℝ) ^ η * (q₂.divisors.card : ℝ) *
          (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2)) :=
        mul_le_mul_of_nonneg_left (exceptional_divisor_sum_le q₁ q₂ hq₁ hq₂ η U hη.le hU0)
          hB.le
      _ = _ := by ring
  have hthree : ((q₁ * q₂ : ℕ) : ℝ) ^ η * ((q₁ * q₂ : ℕ) : ℝ) ^ η *
      ((q₁ * q₂ : ℕ) : ℝ) ^ η = ((q₁ * q₂ : ℕ) : ℝ) ^ ε := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    congr 1
    dsimp [η]
    ring
  calc
    _ ≤ (K ^ q₂.primeFactors.card * (q₂ : ℝ) ^ (3 / 2 : ℝ)) *
        ∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
          weightedCongruenceEuclideanSum A D q₁ h U :=
      weightedSum_le_exceptional_divisors A D q₁ q₂ U
        (K ^ q₂.primeFactors.card * (q₂ : ℝ) ^ (3 / 2 : ℝ)) f hmajor
    _ ≤ (K ^ q₂.primeFactors.card * (q₂ : ℝ) ^ (3 / 2 : ℝ)) *
        (B * ((q₁ * q₂ : ℕ) : ℝ) ^ η * (q₂.divisors.card : ℝ) *
          (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((C₁ * ((q₁ * q₂ : ℕ) : ℝ) ^ η) * (q₂ : ℝ) ^ (3 / 2 : ℝ)) *
        (B * ((q₁ * q₂ : ℕ) : ℝ) ^ η *
          (C₂ * ((q₁ * q₂ : ℕ) : ℝ) ^ η) *
          (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2)) := by
      gcongr
    _ = (B * C₁ * C₂) *
        (((q₁ * q₂ : ℕ) : ℝ) ^ η * ((q₁ * q₂ : ℕ) : ℝ) ^ η *
          ((q₁ * q₂ : ℕ) : ℝ) ^ η) * (q₂ : ℝ) ^ (3 / 2 : ℝ) *
          (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by ring
    _ = _ := by rw [hthree]

end QuaternaryQuadraticForms
