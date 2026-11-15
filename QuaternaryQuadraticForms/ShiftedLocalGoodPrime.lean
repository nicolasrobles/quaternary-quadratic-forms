import QuaternaryQuadraticForms.ShiftedLocalConvergence
import QuaternaryQuadraticForms.LocalDensityGoodPrime

/-!
# Exact shifted factors at good primes

The prime-power coefficients supplied by the existing local calculation form
a geometric series after damping. Its sum gives the shifted Euler factor.
Both numerator and denominator remain nonzero for every nonnegative shift.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The damped geometric ratio still has norm strictly less than one. -/
theorem shiftedLocalDensity_goodPrime_ratio_norm_lt_one (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hz : 0 ≤ z) :
    ‖((legendreSym p A.det : ℂ) / (p : ℂ)) *
      ((((p : ℝ) ^ (-z) : ℝ)) : ℂ)‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (shiftedLocalDensity_damping_norm_le_one p z hz)).trans_lt
      (localDensity_goodPrime_ratio_norm_lt_one p A)

/-- The good-prime geometric ratio in the real-power normalization. -/
theorem shiftedLocalDensity_goodPrime_div_norm_lt_one (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hz : 0 ≤ z) :
    ‖(legendreSym p A.det : ℂ) /
      ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ)‖ < 1 := by
  have hratio := div_natCast_rpow_nat_add p (legendreSym p A.det : ℂ) 1 z
  rw [Nat.cast_one, pow_one] at hratio
  rw [hratio]
  exact shiftedLocalDensity_goodPrime_ratio_norm_lt_one p A z hz

/-- The denominator of the shifted good-prime factor is nonzero. -/
theorem shiftedLocalDensity_goodPrime_den_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hz : 0 ≤ z) :
    1 - (legendreSym p A.det : ℂ) /
      ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ) ≠ 0 := by
  intro h
  have heq := (sub_eq_zero.mp h).symm
  have hn := shiftedLocalDensity_goodPrime_div_norm_lt_one p A z hz
  simp only [heq, norm_one, lt_self_iff_false] at hn

/-- The shifted good-prime coefficients form the exact damped geometric series. -/
theorem shiftedLocalDensityTerm_goodPrime_succ (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) (z : ℝ) :
    shiftedLocalDensityTerm p A z (k + 1) =
      (1 - 1 / (p : ℂ)) *
        (((legendreSym p A.det : ℂ) / (p : ℂ)) *
          ((((p : ℝ) ^ (-z) : ℝ)) : ℂ)) ^ (k + 1) := by
  rw [shiftedLocalDensityTerm, localDensityTerm_goodPrime_succ p k A hA hp, mul_pow]
  ring

/-- Exact summation of the actual good-prime local series at every
nonnegative real shift. -/
theorem shiftedLocalDensityTerm_hasSum_goodPrime (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) (z : ℝ) (hz : 0 ≤ z) :
    HasSum (shiftedLocalDensityTerm p A z)
      ((1 - (legendreSym p A.det : ℂ) /
        ((((p : ℝ) ^ (2 + z) : ℝ)) : ℂ)) /
        (1 - (legendreSym p A.det : ℂ) /
          ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ))) := by
  let r : ℂ := ((legendreSym p A.det : ℂ) / (p : ℂ)) *
    ((((p : ℝ) ^ (-z) : ℝ)) : ℂ)
  have hr : ‖r‖ < 1 := shiftedLocalDensity_goodPrime_ratio_norm_lt_one p A z hz
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have heq := (sub_eq_zero.mp h).symm
    simp only [heq, norm_one, lt_self_iff_false] at hr
  have ht : HasSum (fun k => shiftedLocalDensityTerm p A z (k + 1))
      (((1 - 1 / (p : ℂ)) * r) * (1 - r)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hr).mul_left
      ((1 - 1 / (p : ℂ)) * r) using 1
    ext k
    rw [shiftedLocalDensityTerm_goodPrime_succ p k A hA hp z, pow_succ]
    dsimp [r]
    ring
  have hfull := (hasSum_nat_add_iff 1).mp ht
  simp only [Finset.sum_range_one, shiftedLocalDensityTerm, localDensityTerm_zero,
    pow_zero, mul_one] at hfull
  have hratio : (legendreSym p A.det : ℂ) /
      ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ) = r := by
    simpa [r] using div_natCast_rpow_nat_add p (legendreSym p A.det : ℂ) 1 z
  have hratio₂ : (legendreSym p A.det : ℂ) /
      ((((p : ℝ) ^ (2 + z) : ℝ)) : ℂ) = r / (p : ℂ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      div_natCast_rpow_nat_add]
    dsimp [r]
    ring
  convert hfull using 1
  rw [hratio, hratio₂]
  field_simp [hr1, hp0]
  ring

/-- The shifted local factor at a good prime has the stated Euler quotient. -/
theorem shiftedLocalDensity_goodPrime (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) (z : ℝ) (hz : 0 ≤ z) :
    shiftedLocalDensity p A z =
      (1 - (legendreSym p A.det : ℂ) /
        ((((p : ℝ) ^ (2 + z) : ℝ)) : ℂ)) /
        (1 - (legendreSym p A.det : ℂ) /
          ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ)) :=
  (shiftedLocalDensityTerm_hasSum_goodPrime p A hA hp z hz).tsum_eq

/-- The numerator also has norm separation from zero, since it is the
geometric denominator at shift `1 + z`. -/
theorem shiftedLocalDensity_goodPrime_num_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hz : 0 ≤ z) :
    1 - (legendreSym p A.det : ℂ) /
      ((((p : ℝ) ^ (2 + z) : ℝ)) : ℂ) ≠ 0 := by
  have he : (1 : ℝ) + (1 + z) = 2 + z := by ring
  simpa only [he] using
    shiftedLocalDensity_goodPrime_den_ne_zero p A (1 + z) (by linarith)

/-- Every good-prime shifted local factor is nonzero for `z ≥ 0`. -/
theorem shiftedLocalDensity_goodPrime_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) (z : ℝ) (hz : 0 ≤ z) :
    shiftedLocalDensity p A z ≠ 0 := by
  rw [shiftedLocalDensity_goodPrime p A hA hp z hz]
  exact div_ne_zero (shiftedLocalDensity_goodPrime_num_ne_zero p A z hz)
    (shiftedLocalDensity_goodPrime_den_ne_zero p A z hz)

/-- The exact good-prime quotient using the manuscript's original character. -/
theorem source_shiftedLocalDensity_goodPrime (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (hp : ¬p ∣ quadraticBadPrimeModulus A) (z : ℝ) (hz : 0 ≤ z) :
    shiftedLocalDensity p A z =
      (1 - χ (p : ZMod M) / ((((p : ℝ) ^ (2 + z) : ℝ)) : ℂ)) /
        (1 - χ (p : ZMod M) / ((((p : ℝ) ^ (1 + z) : ℝ)) : ℂ)) := by
  rw [hχ p hp]
  exact shiftedLocalDensity_goodPrime p A hA hp z hz

end QuaternaryQuadraticForms
