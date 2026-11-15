import QuaternaryQuadraticForms.SingularSeriesDefinitions
import QuaternaryQuadraticForms.BadPrimeBound
import QuaternaryQuadraticForms.CompleteSumFactorization
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Absolutely convergent shifted singular series

For every positive real shift, the actual coprime-restricted complete sums
are absolutely summable. Their Euler product follows from the proved CRT
identity for the complete sums and mathlib's multiplicative Euler-product
theorem. No convergence claim is made here at shift zero.
-/

noncomputable section

namespace QuaternaryQuadraticForms

attribute [local simp] coprimeCompleteSumValue_zero singularSeriesTerm_zero

@[simp]
theorem coprimeCompleteSumValue_one (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) : coprimeCompleteSumValue q A 1 = 1 := by
  simp [coprimeCompleteSumValue, unweightedCompleteSumValue_of_neZero,
    unweightedCompleteSum_one]

/-- The gcd restriction preserves the actual CRT multiplicativity. -/
theorem coprimeCompleteSumValue_mul (q m n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hmn : m.Coprime n) :
    coprimeCompleteSumValue q A (m * n) =
      coprimeCompleteSumValue q A m * coprimeCompleteSumValue q A n := by
  by_cases hm0 : m = 0
  · simp [hm0]
  by_cases hn0 : n = 0
  · simp [hn0]
  letI : NeZero m := ⟨hm0⟩
  letI : NeZero n := ⟨hn0⟩
  by_cases hmq : m.Coprime q
  · by_cases hnq : n.Coprime q
    · simp only [coprimeCompleteSumValue,
        if_pos (Nat.coprime_mul_iff_left.mpr ⟨hmq, hnq⟩), if_pos hmq, if_pos hnq,
        unweightedCompleteSumValue_of_neZero]
      exact unweightedCompleteSum_mul m n A 0 hmn
    · have hmnq : ¬(m * n).Coprime q := fun h => hnq (Nat.coprime_mul_iff_left.mp h).2
      simp only [coprimeCompleteSumValue, if_neg hmnq, if_neg hnq, mul_zero]
  · have hmnq : ¬(m * n).Coprime q := fun h => hmq (Nat.coprime_mul_iff_left.mp h).1
    simp only [coprimeCompleteSumValue, if_neg hmnq, if_neg hmq, zero_mul]

/-- The uniform complete-sum bound remains valid after the gcd restriction. -/
theorem coprimeCompleteSumValue_norm_le (q c : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    ‖coprimeCompleteSumValue q A c‖ ≤
      4 * Real.sqrt |(A.det : ℝ)| * (c : ℝ) ^ 3 := by
  by_cases hc0 : c = 0
  · simp [hc0]
  letI : NeZero c := ⟨hc0⟩
  by_cases hcq : c.Coprime q
  · simpa only [coprimeCompleteSumValue, if_pos hcq,
      unweightedCompleteSumValue_of_neZero] using bad_prime_bound c A hA hdet 0
  · simp only [coprimeCompleteSumValue, if_neg hcq, norm_zero]
    positivity

@[simp]
theorem singularSeriesTerm_one (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) : singularSeriesTerm q A z 1 = 1 := by
  simp [singularSeriesTerm]

/-- Multiplicativity of the actual shifted summand, including zero moduli. -/
theorem singularSeriesTerm_mul (q m n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hmn : m.Coprime n) :
    singularSeriesTerm q A z (m * n) =
      singularSeriesTerm q A z m * singularSeriesTerm q A z n := by
  simp only [singularSeriesTerm, coprimeCompleteSumValue_mul q m n A hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
    Complex.ofReal_mul]
  exact mul_div_mul_comm _ _ _ _

/-- The absolute shifted summand is bounded by an ordinary convergent
`p`-series when `z > 0`. The constant depends only on the determinant. -/
theorem singularSeriesTerm_norm_le (q c : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) :
    ‖singularSeriesTerm q A z c‖ ≤
      (4 * Real.sqrt |(A.det : ℝ)|) * (c : ℝ) ^ (-1 - z) := by
  by_cases hc0 : c = 0
  · rw [hc0, singularSeriesTerm_zero, norm_zero]
    positivity
  have hcpos : 0 < (c : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc0)
  have hpow : (c : ℝ) ^ 3 / (c : ℝ) ^ (4 + z) = (c : ℝ) ^ (-1 - z) := by
    calc
      _ = (c : ℝ) ^ ((3 : ℝ) - (4 + z)) := by
        simp only [Real.rpow_sub hcpos, Real.rpow_ofNat]
      _ = _ := by congr 1; ring
  calc
    ‖singularSeriesTerm q A z c‖ =
        ‖coprimeCompleteSumValue q A c‖ / (c : ℝ) ^ (4 + z) := by
      rw [singularSeriesTerm, norm_div, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hcpos.le _)]
    _ ≤ (4 * Real.sqrt |(A.det : ℝ)| * (c : ℝ) ^ 3) /
        (c : ℝ) ^ (4 + z) :=
      div_le_div_of_nonneg_right (coprimeCompleteSumValue_norm_le q c A hA hdet)
        (Real.rpow_nonneg hcpos.le _)
    _ = _ := by rw [mul_div_assoc, hpow]

/-- Absolute convergence of the actual shifted series for every positive
shift. This holds for every natural `q`, without squarefreeness assumptions. -/
theorem summable_norm_singularSeriesTerm (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) : Summable (fun c : ℕ => ‖singularSeriesTerm q A z c‖) := by
  have hp : Summable (fun c : ℕ => (c : ℝ) ^ (-1 - z)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (hp.mul_left (4 * Real.sqrt |(A.det : ℝ)|)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun c => singularSeriesTerm_norm_le q c A hA hdet z)

/-- The actual singular-series summand is summable for positive shift. -/
theorem summable_singularSeriesTerm (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) : Summable (singularSeriesTerm q A z) :=
  (summable_norm_singularSeriesTerm q A hA hdet z hz).of_norm

/-- The complete Euler product of the actual coprime-restricted shifted
series. Its factors are actual prime-power character sums. -/
theorem singularSeriesTerm_eulerProduct_hasProd (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) :
    HasProd (fun p : Nat.Primes => ∑' k : ℕ, singularSeriesTerm q A z ((p : ℕ) ^ k))
      (∑' c : ℕ, singularSeriesTerm q A z c) := by
  exact EulerProduct.eulerProduct_hasProd (singularSeriesTerm_one q A z)
    (fun {m n} hmn => singularSeriesTerm_mul q m n A z hmn)
    (summable_norm_singularSeriesTerm q A hA hdet z hz)
    (singularSeriesTerm_zero q A z)

end QuaternaryQuadraticForms
