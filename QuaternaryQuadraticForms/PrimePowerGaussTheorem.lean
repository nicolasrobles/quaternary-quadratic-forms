import QuaternaryQuadraticForms.UnramifiedCompleteSum
import QuaternaryQuadraticForms.QuadricPointCount

/-!
# Complete Lemma 3.2

All three conclusions use the source integral matrix and its exact good-prime
modulus. The character at a good prime is the stated Legendre symbol of the
determinant. No Gauss evaluation, recurrence, unit-sum formula, or point-count
identity is assumed in the final theorem.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Every clause of Lemma 3.2 for the literal source form: the full shifted
Gauss evaluation, the exact Ramanujan formula, and the projective quadric count. -/
theorem prime_power_gauss (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ) :
    (∀ a : ℤ, ¬ (p : ℤ) ∣ a →
      integralQuadraticGaussSum (p ^ k) A a u =
        (legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k) *
          ZMod.stdAddChar (-((4 * a * A.det : ℤ) : ZMod (p ^ k))⁻¹ *
            ((dotProduct u (A.adjugate.mulVec u) : ℤ) : ZMod (p ^ k)))) ∧
    (unweightedCompleteSum (p ^ k) A u =
      ((legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k)) *
        integralRamanujanSum (p ^ k) (dotProduct u (A.adjugate.mulVec u))) ∧
    (((projectiveQuadric (reduceQuadraticMatrix p A)).card : ℤ) =
      (p : ℤ) ^ 2 + (1 + legendreSym p A.det) * p + 1) :=
  ⟨fun a ha => integralQuadraticGaussSum_prime_power p k A hA hp a ha u,
    unweightedCompleteSum_prime_power p k hk A hA hp u,
    integral_projectiveQuadric_card p A hA hp⟩

end QuaternaryQuadraticForms
