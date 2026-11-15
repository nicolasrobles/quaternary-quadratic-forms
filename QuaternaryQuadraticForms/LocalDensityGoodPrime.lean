import QuaternaryQuadraticForms.LocalDensityDefinitions
import QuaternaryQuadraticForms.GoodUnweightedCompleteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The exact local series at a good prime

The coefficients are the existing complete sums. Their prime-power evaluation
and the actual Euler totient give a geometric series, including its separate
modulus-one term. No value or convergence of the local density is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exponent-zero term is the actual modulus-one complete sum. -/
@[simp]
theorem localDensityTerm_zero (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) : localDensityTerm p A 0 = 1 := by
  simp [localDensityTerm, unweightedCompleteSum_one]

/-- The source Legendre coefficient has complex norm at most one. -/
theorem legendreSym_complex_norm_le_one (p : ℕ) [Fact p.Prime] (a : ℤ) :
    ‖(legendreSym p a : ℂ)‖ ≤ 1 := by
  rw [← globalQuadraticChar_prime]
  rcases jacobiSym.trichotomy a p with h | h | h <;>
    simp [globalQuadraticChar, h]

/-- The ratio of the good-prime geometric series has norm strictly below one. -/
theorem localDensity_goodPrime_ratio_norm_lt_one (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    ‖(legendreSym p A.det : ℂ) / (p : ℂ)‖ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (legendreSym_complex_norm_le_one p A.det)
    (by positivity)).trans_lt ((div_lt_one (by positivity)).mpr hp)

/-- At every positive exponent the actual coefficient is the stated
geometric term, with no determinant or character value cancelled. -/
theorem localDensityTerm_goodPrime_succ (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    localDensityTerm p A (k + 1) =
      (1 - 1 / (p : ℂ)) * ((legendreSym p A.det : ℂ) / (p : ℂ)) ^ (k + 1) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [localDensityTerm, unweightedCompleteSum_prime_power p (k + 1) (by omega)
    A hA hp]
  simp only [Matrix.mulVec_zero, dotProduct_zero, integralRamanujanSum_zero,
    Nat.totient_prime_pow_succ (Fact.out : p.Prime), Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hp1, Nat.cast_one]
  have h2 : (p : ℂ) ^ (2 * (k + 1)) = (p ^ k : ℂ) ^ 2 * p ^ 2 := by
    rw [Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm 2 k, pow_mul]
  have h4 : (p : ℂ) ^ (4 * (k + 1)) = (p ^ k : ℂ) ^ 4 * p ^ 4 := by
    rw [Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm 4 k, pow_mul]
  rw [h2, h4, div_pow, pow_succ (p : ℂ) k]
  field_simp

/-- The good-prime local series has exactly the rational value in
`eq:sigmagood`. The denominator is nonzero by the geometric ratio bound. -/
theorem localDensityTerm_hasSum_goodPrime (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    HasSum (localDensityTerm p A)
      ((1 - (legendreSym p A.det : ℂ) / (p : ℂ) ^ 2) /
        (1 - (legendreSym p A.det : ℂ) / (p : ℂ))) := by
  let r : ℂ := (legendreSym p A.det : ℂ) / (p : ℂ)
  have hr : ‖r‖ < 1 := localDensity_goodPrime_ratio_norm_lt_one p A
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have h' : r = 1 := (sub_eq_zero.mp h).symm
    simp [h'] at hr
  have ht : HasSum (fun k => localDensityTerm p A (k + 1))
      (((1 - 1 / (p : ℂ)) * r) * (1 - r)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hr).mul_left ((1 - 1 / (p : ℂ)) * r)
      using 1
    ext k
    rw [localDensityTerm_goodPrime_succ p k A hA hp, pow_succ]
    dsimp [r]
    ring
  have hfull := (hasSum_nat_add_iff 1).mp ht
  simp only [Finset.sum_range_one, localDensityTerm_zero] at hfull
  convert hfull using 1
  dsimp [r] at hr1 ⊢
  have hpa : (p : ℂ) - (legendreSym p A.det : ℂ) ≠ 0 := by
    intro h
    apply hr1
    rw [← sub_eq_zero.mp h, div_self hp0, sub_self]
  field_simp [hpa]
  ring

end QuaternaryQuadraticForms
