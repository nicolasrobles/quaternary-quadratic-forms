import QuaternaryQuadraticForms.LocalDensityDefinitions
import QuaternaryQuadraticForms.BadPrimeBound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute convergence of every local density series

The uniform complete-sum bound applies at all prime powers, including powers
of two and of the bad primes. Dividing by the exact fourth-power normalization
gives a summable geometric majorant. No local nonsingularity is required.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual local coefficient has the uniform geometric majorant supplied
by Lemma 3.3, including the coefficient at exponent zero. -/
theorem localDensityTerm_norm_le (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (k : ℕ) :
    ‖localDensityTerm p A k‖ ≤
      4 * Real.sqrt |(A.det : ℝ)| * (1 / (p : ℝ)) ^ k := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hb := bad_prime_bound (p ^ k) A hA hdet 0
  rw [localDensityTerm, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (4 * Real.sqrt |(A.det : ℝ)| * (p : ℝ) ^ (3 * k)) /
        (p : ℝ) ^ (4 * k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm k 3] using hb
    _ = (4 * Real.sqrt |(A.det : ℝ)| * (p : ℝ) ^ (3 * k)) /
        ((p : ℝ) ^ (3 * k) * (p : ℝ) ^ k) := by
      rw [← pow_add]
      congr 2
      omega
    _ = (4 * Real.sqrt |(A.det : ℝ)|) / (p : ℝ) ^ k := by
      rw [mul_comm (4 * Real.sqrt |(A.det : ℝ)|) _,
        mul_div_mul_left _ _ (pow_ne_zero _ hp)]
    _ = _ := by rw [one_div_pow, div_eq_mul_inv, one_div]

/-- The local series is absolutely convergent at every prime, with no
restriction on whether that prime divides the determinant. -/
theorem summable_norm_localDensityTerm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Summable (fun k : ℕ => ‖localDensityTerm p A k‖) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hg : Summable (fun k : ℕ => (1 / (p : ℝ)) ^ k) :=
    summable_geometric_of_lt_one (by positivity) ((div_lt_one (by positivity)).2 hp)
  exact (hg.mul_left (4 * Real.sqrt |(A.det : ℝ)|)).of_nonneg_of_le
    (fun k => norm_nonneg (localDensityTerm p A k))
    (fun k => localDensityTerm_norm_le p A hA hdet k)

/-- The literal complex local complete-sum series is summable at every prime. -/
theorem summable_localDensityTerm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Summable (localDensityTerm p A) :=
  (summable_norm_localDensityTerm p A hA hdet).of_norm

end QuaternaryQuadraticForms
