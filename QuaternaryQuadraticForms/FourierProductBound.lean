import QuaternaryQuadraticForms.CompleteSumFactorization
import QuaternaryQuadraticForms.FourierDivisorExpansion

/-!
# The actual Fourier sum and its exceptional-divisor bound

The existing CRT theorem supplies the prime product of the actual
constrained Fourier sum. The assumed local two-level estimate is exactly
the hypothesis (3.3) of Section 3. Expanding its exceptional factors gives
the divisor bound (3.32), with the original polynomial indicators.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem local_fourier_factor (p d : ℝ) (hp : 0 < p) :
    p ^ (3 / 2 : ℝ) + p ^ 2 * d =
      p ^ (3 / 2 : ℝ) * (1 + p ^ (1 / 2 : ℝ) * d) := by
  have hpow : p ^ (3 / 2 : ℝ) * p ^ (1 / 2 : ℝ) = p ^ 2 := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = p ^ (3 / 2 : ℝ) +
        (p ^ (3 / 2 : ℝ) * p ^ (1 / 2 : ℝ)) * d := by rw [hpow]
    _ = _ := by ring

/-- The product of the local stratified bounds has the precise divisor
expansion in the manuscript. This is an equality of actual local indicators. -/
theorem fourier_stratified_product_eq
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q : ℕ) (hsq : Squarefree q) (u : Fin 4 → ℤ) (K : ℝ) :
    (∏ p ∈ q.primeFactors,
      K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
        (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0))) =
      K ^ q.primeFactors.card * (q : ℝ) ^ (3 / 2 : ℝ) *
        ∑ h ∈ q.divisors, (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u := by
  classical
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) :
      K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
        (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0)) =
      (K * (p : ℝ) ^ (3 / 2 : ℝ)) *
        (1 + (p : ℝ) ^ (1 / 2 : ℝ) *
          (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0)) := by
    rw [local_fourier_factor _ _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)]
    ring
  have hpower : (∏ p ∈ q.primeFactors, (p : ℝ) ^ (3 / 2 : ℝ)) =
      (q : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p) (3 / 2 : ℝ),
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [Finset.prod_congr rfl hlocal, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, hpower,
    exceptional_prime_product_eq_divisor_sum D q hsq u]

/-- The actual constrained Fourier sum satisfies equation (3.32).
Only the local bounds at the prime divisors of this squarefree modulus
are assumed; its CRT product is supplied by the proved complete-sum theorem. -/
theorem constrainedFourierSum_norm_le_divisors
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q : ℕ) [NeZero q] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (K : ℝ) (hsq : Squarefree q) (hξ : PrimeWeightsInvariant ξ q)
    (hlocal : ∀ p (hp : p ∈ q.primeFactors),
      ‖@constrainedFourierSum ξ p ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩ A u‖ ≤
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0))) :
    ‖constrainedFourierSum ξ q A u‖ ≤
      K ^ q.primeFactors.card * (q : ℝ) ^ (3 / 2 : ℝ) *
        ∑ h ∈ q.divisors, (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u := by
  classical
  rw [constrainedFourierSum_primeFactors ξ q A u hsq hξ, norm_prod]
  calc
    _ ≤ ∏ p : q.primeFactors,
        K * ((p.val : ℝ) ^ (3 / 2 : ℝ) + (p.val : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun i => (u i : ZMod p.val)) (D p.val) = 0
            then 1 else 0)) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p _
      exact hlocal p.val p.property
    _ = ∏ p ∈ q.primeFactors,
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0)) := by
      exact Finset.prod_coe_sort q.primeFactors (fun p : ℕ =>
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0)))
    _ = _ := fourier_stratified_product_eq D q hsq u K

end QuaternaryQuadraticForms
