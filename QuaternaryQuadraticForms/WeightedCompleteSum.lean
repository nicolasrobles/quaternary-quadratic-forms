import QuaternaryQuadraticForms.WeightedGaussSums
import QuaternaryQuadraticForms.UnramifiedCompleteSum
import QuaternaryQuadraticForms.WeightedGaussExtraction

/-!
# Assembly of the prime-weighted complete sum

The outer unit sum preserves a common factor of the actual inner Gauss
sums. The proved stationary-residue argument supplies the precise source
weight, and the existing complete Gauss evaluation gives `𝒰_j`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A common factor of the literal inner sums factors from the actual unit sum. -/
theorem primeWeightedCompleteSum_of_gauss_factor
    (p n : ℕ) [NeZero n] (ξ : (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (C : ℂ)
    (hC : ∀ a : (ZMod n)ˣ,
      weightedIntegralGaussSum p n ξ A (((a : ZMod n).val : ℕ) : ℤ) u =
        C * integralQuadraticGaussSum n A (((a : ZMod n).val : ℕ) : ℤ) u) :
    primeWeightedCompleteSum p n ξ A u = C * unweightedCompleteSum n A u := by
  simp only [primeWeightedCompleteSum, hC,
    unweightedCompleteSum_eq_sum_integralQuadraticGaussSum, Finset.mul_sum]

private theorem unit_lift_not_dvd_prime (p j : ℕ) [Fact p.Prime]
    (hj : 1 ≤ j) (a : (ZMod (p ^ j))ˣ) :
    ¬ (p : ℤ) ∣ (((a : ZMod (p ^ j)).val : ℕ) : ℤ) := by
  have hcop : ((a : ZMod (p ^ j)).val).Coprime p :=
    (ZMod.val_coe_unit_coprime a).of_dvd_right (dvd_pow_self p (by omega))
  intro h
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop.symm)
    (Int.natCast_dvd_natCast.mp h)

/-- The actual weighted complete sum factors by the source adjugate weight
at every prime power of exponent at least two. -/
theorem primeWeightedCompleteSum_prime_power_factor
    (p j : ℕ) [Fact p.Prime] (hj : 2 ≤ j)
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p, ξ (r • y) = ξ y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ) :
    primeWeightedCompleteSum p (p ^ j) ξ A u =
      ξ (reduceFrequency p (A.adjugate.mulVec u)) *
        unweightedCompleteSum (p ^ j) A u := by
  apply primeWeightedCompleteSum_of_gauss_factor
  intro a
  exact weightedIntegralGaussSum_prime_power_extract p j hj ξ hξ A hA hp
    (((a : ZMod (p ^ j)).val : ℕ) : ℤ)
    (unit_lift_not_dvd_prime p j (by omega) a) u

/-- The exact formula `𝒰_j` from the proof of Lemma 3.4, with the actual
weight, Legendre symbol, adjugate dual value, and Ramanujan sum. -/
theorem primeWeightedCompleteSum_prime_power
    (p j : ℕ) [Fact p.Prime] (hj : 2 ≤ j)
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p, ξ (r • y) = ξ y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ) :
    primeWeightedCompleteSum p (p ^ j) ξ A u =
      (legendreSym p A.det : ℂ) ^ j * (p : ℂ) ^ (2 * j) *
        ξ (reduceFrequency p (A.adjugate.mulVec u)) *
          integralRamanujanSum (p ^ j) (dotProduct u (A.adjugate.mulVec u)) := by
  rw [primeWeightedCompleteSum_prime_power_factor p j hj ξ hξ A hA hp u,
    unweightedCompleteSum_prime_power p j (by omega) A hA hp u]
  ring

end QuaternaryQuadraticForms
