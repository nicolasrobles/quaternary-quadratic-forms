import QuaternaryQuadraticForms.PrimePowerGauss
import QuaternaryQuadraticForms.GaussRamanujan

/-!
# The exact complete sum at every good prime power

The proved pure Gauss value is constant over the actual unit group.
Square completion and its reciprocal unit permutation give the literal
Ramanujan sum at the adjugate dual value.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Lemma 3.2(ii), with the actual complete sum, actual Ramanujan unit
sum, and the manuscript's integral determinant and adjugate dual form. -/
theorem unweightedCompleteSum_prime_power (p k : ℕ) [Fact p.Prime]
    (hk : 1 ≤ k) (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ) :
    unweightedCompleteSum (p ^ k) A u =
      ((legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k)) *
        integralRamanujanSum (p ^ k) (dotProduct u (A.adjugate.mulVec u)) := by
  apply unweightedCompleteSum_of_constant_gauss (p ^ k) A hA u
  · exact goodPrime_two_isUnit_prime_pow p k A hp
  · exact intCast_isUnit_prime_pow p k A.det (goodPrime_not_dvd_det p A hp)
  · intro a
    exact quadraticGaussSum_prime_power_units_pure p k hk A hA hp a

end QuaternaryQuadraticForms
