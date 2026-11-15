import QuaternaryQuadraticForms.SingularSeriesConstant
import QuaternaryQuadraticForms.SourceFourierSums
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Local bounds for the actual main coefficient

At a good prime the previously proved density formula bounds its inverse
uniformly.  The source two-stratum Fourier estimate bounds the zero-frequency
sum regardless of the exceptional polynomial's value at zero.  These two
facts give the local factor bound used in the squarefree prime product.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual counting density is strictly positive at every good prime. -/
theorem localQuadraticDensity_goodPrime_pos (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    0 < localQuadraticDensity p A := by
  have hn : localQuadraticDensity p A ≠ 0 := by
    intro hz
    apply localQuadraticDensity_goodPrime_ne_zero p A hA hdet hp
    simp only [hz, Complex.ofReal_zero]
  exact lt_of_le_of_ne (localQuadraticDensity_nonneg p A hA hdet) (Ne.symm hn)

/-- The reciprocal of the actual good-prime density has complex norm at
most two. The bound follows from the exact formula and the Legendre norm. -/
theorem localQuadraticDensity_goodPrime_inv_norm_le_two (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    ‖(localQuadraticDensity p A : ℂ)⁻¹‖ ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hchar := legendreSym_complex_norm_le_one p A.det
  have hratio : ‖(legendreSym p A.det : ℂ) / (p : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hp0).2
    linarith
  have hratio2 : ‖(legendreSym p A.det : ℂ) / (p : ℂ) ^ 2‖ ≤ (1 / 4 : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith
  have hnum : ‖1 - (legendreSym p A.det : ℂ) / (p : ℂ)‖ ≤ (3 / 2 : ℝ) := by
    have hn := norm_sub_le (1 : ℂ) ((legendreSym p A.det : ℂ) / (p : ℂ))
    simp only [norm_one] at hn
    linarith
  have hden : (3 / 4 : ℝ) ≤ ‖1 - (legendreSym p A.det : ℂ) / (p : ℂ) ^ 2‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) ((legendreSym p A.det : ℂ) / (p : ℂ) ^ 2)
    simp only [norm_one] at hn
    linarith
  rw [localQuadraticDensity_goodPrime p A hA hdet hp, inv_div, norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) hden)).2
  linarith

/-- The real reciprocal satisfies the same uniform good-prime bound. -/
theorem localQuadraticDensity_goodPrime_inv_le_two (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    (localQuadraticDensity p A)⁻¹ ≤ 2 := by
  have h := localQuadraticDensity_goodPrime_inv_norm_le_two p A hA hdet hp
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- The actual zero-frequency sum is bounded in both source strata. In
particular, no vanishing assumption on `D(0)` is needed. -/
theorem sourceConstrainedFourierSum_zero_norm_le_two_mul_sq
    (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p ∣ N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (D : MvPolynomial (Fin 4) (ZMod p))
    (K : ℝ) (hK : 0 ≤ K)
    (hlocal :
      ‖sourceConstrainedFourierSum N ξ p
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN) A 0‖ ≤
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) D = 0 then 1 else 0))) :
    ‖sourceConstrainedFourierSum N ξ p
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN) A 0‖ ≤
      2 * K * (p : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hpow : (p : ℝ) ^ (3 / 2 : ℝ) ≤ (p : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (3 / 2 : ℝ) ≤ (2 : ℝ))
  have hind : (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) D = 0
      then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  calc
    _ ≤ K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
        (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) D = 0 then 1 else 0)) :=
      hlocal
    _ ≤ K * ((p : ℝ) ^ 2 + (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact add_le_add hpow (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hind (sq_nonneg (p : ℝ)))
    _ = 2 * K * (p : ℝ) ^ 2 := by ring

/-- The actual local main-coefficient factor is bounded by `4K/p`,
using only the stated source Fourier stratum estimate. -/
theorem sourceMainCoefficient_local_norm_le
    (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p ∣ N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A)
    (D : MvPolynomial (Fin 4) (ZMod p)) (K : ℝ) (hK : 0 ≤ K)
    (hlocal :
      ‖sourceConstrainedFourierSum N ξ p
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN) A 0‖ ≤
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) D = 0 then 1 else 0))) :
    ‖sourceConstrainedFourierSum N ξ p
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN) A 0 /
      ((p : ℂ) ^ 3 * (localQuadraticDensity p A : ℂ))‖ ≤ 4 * K / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hC := sourceConstrainedFourierSum_zero_norm_le_two_mul_sq N ξ p hpN A D K hK hlocal
  have hσ := localQuadraticDensity_goodPrime_inv_norm_le_two p A hA hdet hp
  rw [← div_div, div_eq_mul_inv _ (localQuadraticDensity p A : ℂ),
    norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (2 * K * (p : ℝ) ^ 2 / (p : ℝ) ^ 3) * 2 :=
      mul_le_mul (div_le_div_of_nonneg_right hC (by positivity)) hσ
        (norm_nonneg _) (by positivity)
    _ = 4 * K / (p : ℝ) := by
      field_simp
      ring

end QuaternaryQuadraticForms
