import QuaternaryQuadraticForms.IntegralGaussSums

/-!
# The literal prime-weighted Gauss and complete sums

The weight is evaluated on the reduction modulo `p` of each canonical
integer vector. The ambient modulus is a separate parameter, so that the
source's sum `𝒰_j` is obtained by taking that modulus to be `p ^ j`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual integral Gauss sum with a supplied weight modulo `p`. -/
def weightedIntegralGaussSum (p n : ℕ) [NeZero n]
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ x : Fin 4 → ZMod n,
    ξ (fun i => (residueLift n x i : ZMod p)) *
      ZMod.stdAddChar ((a * integralQuadraticValue A (residueLift n x) +
        dotProduct u (residueLift n x) : ℤ) : ZMod n)

/-- The actual unit sum whose prime-power specialization is `𝒰_j`. -/
def primeWeightedCompleteSum (p n : ℕ) [NeZero n]
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ a : (ZMod n)ˣ,
    weightedIntegralGaussSum p n ξ A (((a : ZMod n).val : ℕ) : ℤ) u

/-- Constant weight one recovers the existing integral Gauss sum. -/
theorem weightedIntegralGaussSum_one (p n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) :
    weightedIntegralGaussSum p n (fun _ => 1) A a u =
      integralQuadraticGaussSum n A a u := by
  simp only [weightedIntegralGaussSum, integralQuadraticGaussSum_eq_lift_sum, one_mul]

/-- The existing complete sum is the unit sum of its literal integral Gauss sums. -/
theorem unweightedCompleteSum_eq_sum_integralQuadraticGaussSum
    (n : ℕ) [NeZero n] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    unweightedCompleteSum n A u =
      ∑ a : (ZMod n)ˣ,
        integralQuadraticGaussSum n A (((a : ZMod n).val : ℕ) : ℤ) u := by
  simp only [unweightedCompleteSum, integralQuadraticGaussSum_eq_lift_sum]

/-- Constant weight one recovers the manuscript's existing complete sum. -/
theorem primeWeightedCompleteSum_one (p n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    primeWeightedCompleteSum p n (fun _ => 1) A u =
      unweightedCompleteSum n A u := by
  simp only [primeWeightedCompleteSum, weightedIntegralGaussSum_one,
    unweightedCompleteSum_eq_sum_integralQuadraticGaussSum]

end QuaternaryQuadraticForms
