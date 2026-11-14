import QuaternaryQuadraticForms.WeightedCompleteSum
import QuaternaryQuadraticForms.RamifiedUnitLift
import QuaternaryQuadraticForms.SourceGoodPrime
import QuaternaryQuadraticForms.SourceWeights

/-!
# Complete Lemma 3.4

The evaluated weighted complete sum and its actual unit-digit bridge
give the precise shared-prime formula. The source wrapper uses the
original local weight at a prime not dividing `N` and the exact source
radical divisibility condition to supply good quadratic reduction.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The full shared-prime identity for the existing mixed complete sum,
with a scalar-invariant local weight and the literal good-prime modulus. -/
theorem ramified_complete_sum
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p,
      ξ p (r • y) = ξ p y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ p (p ^ k) A u =
      (legendreSym p A.det : ℂ) ^ (k + 1) * (p : ℂ) ^ (2 * k + 1) *
        ξ p (reduceFrequency p (A.adjugate.mulVec u)) *
          integralRamanujanSum (p ^ (k + 1)) (dotProduct u (A.adjugate.mulVec u)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hpC
  calc
    (p : ℂ) * mixedCompleteSum ξ p (p ^ k) A u =
        primeWeightedCompleteSum p (p ^ (k + 1)) (ξ p) A u :=
      (primeWeightedCompleteSum_prime_power_lift p k hk ξ A u).symm
    _ = (legendreSym p A.det : ℂ) ^ (k + 1) * (p : ℂ) ^ (2 * (k + 1)) *
        ξ p (reduceFrequency p (A.adjugate.mulVec u)) *
          integralRamanujanSum (p ^ (k + 1)) (dotProduct u (A.adjugate.mulVec u)) :=
      primeWeightedCompleteSum_prime_power p (k + 1) (by omega) (ξ p) hξ A hA hp u
    _ = _ := by
      have hexp : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hexp, pow_succ (p : ℂ) (2 * k + 1)]
      ring

/-- Lemma 3.4 for the manuscript's supplied local functions: `p ∤ N`
and `rad(N_F) ∣ N` supply every good-prime condition, and the final weight
is the original supplied function at the actual adjugate vector. -/
theorem source_ramified_complete_sum
    (N p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N) (hpN : ¬ p ∣ N)
    (ξ : ∀ q : ℕ, q.Prime → ¬ q ∣ N → (Fin 4 → ZMod q) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p,
      ξ p Fact.out hpN (r • y) = ξ p Fact.out hpN y)
    (u : Fin 4 → ℤ) :
    mixedCompleteSum (extendPrimeWeights N ξ) p (p ^ k) A u =
      (legendreSym p A.det : ℂ) ^ (k + 1) * (p : ℂ) ^ (2 * k + 1) *
        ξ p Fact.out hpN (reduceFrequency p (A.adjugate.mulVec u)) *
          integralRamanujanSum (p ^ (k + 1)) (dotProduct u (A.adjugate.mulVec u)) := by
  have hp := source_not_dvd_quadraticBadPrimeModulus N p A hdet hrad hpN
  have hξ' : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p,
      extendPrimeWeights N ξ p (r • y) = extendPrimeWeights N ξ p y := by
    intro r hr y
    simpa only [extendPrimeWeights_apply N ξ p Fact.out hpN] using hξ r hr y
  simpa only [extendPrimeWeights_apply N ξ p Fact.out hpN] using
    ramified_complete_sum p k hk (extendPrimeWeights N ξ) hξ' A hA hp u

end QuaternaryQuadraticForms
