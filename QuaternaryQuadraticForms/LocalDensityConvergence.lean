import QuaternaryQuadraticForms.LocalDensitySummability
import QuaternaryQuadraticForms.LocalDensityCounting
import Mathlib.Analysis.Complex.Basic

/-!
# The local density is the limit of the actual zero counts

The finite orthogonality identity and the absolute convergence proved earlier
give a limit of the normalized residue counts at every prime. Because those
counts are real and nonnegative, the complete-sum series has a real,
nonnegative value. This value is the density defined from the counting limit.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

private theorem normalized_counts_complex_tendsto (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Tendsto (fun k : ℕ => (normalizedPrimePowerZeroCount p A k : ℂ)) atTop
      (𝓝 (∑' k : ℕ, localDensityTerm p A k)) := by
  have h := (summable_localDensityTerm p A hA hdet).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext k
  exact normalizedPrimePowerZeroCount_eq_sum p k A

private theorem normalized_counts_real_tendsto (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Tendsto (normalizedPrimePowerZeroCount p A) atTop
      (𝓝 (∑' k : ℕ, localDensityTerm p A k).re) := by
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto _).comp
      (normalized_counts_complex_tendsto p A hA hdet)

/-- The local density defined by the actual real counting sequence equals
the real part of the absolutely convergent complete-sum series. -/
theorem localQuadraticDensity_eq_tsum_re (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    localQuadraticDensity p A = (∑' k : ℕ, localDensityTerm p A k).re :=
  (normalized_counts_real_tendsto p A hA hdet).limUnder_eq

/-- The actual normalized number of zeros modulo `p^k` converges to the
source local density at every prime, including all bad primes. -/
theorem tendsto_normalizedPrimePowerZeroCount (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Tendsto (normalizedPrimePowerZeroCount p A) atTop (𝓝 (localQuadraticDensity p A)) := by
  rw [localQuadraticDensity_eq_tsum_re p A hA hdet]
  exact normalized_counts_real_tendsto p A hA hdet

/-- The literal complex complete-sum series has sum equal to the real
density defined by the normalized counts. Its reality is proved by uniqueness
of the limit of those actual counts. -/
theorem hasSum_localDensityTerm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    HasSum (localDensityTerm p A) (localQuadraticDensity p A : ℂ) := by
  have hc := (Complex.continuous_ofReal.tendsto (localQuadraticDensity p A)).comp
    (tendsto_normalizedPrimePowerZeroCount p A hA hdet)
  have heq : (∑' k : ℕ, localDensityTerm p A k) = (localQuadraticDensity p A : ℂ) :=
    tendsto_nhds_unique (normalized_counts_complex_tendsto p A hA hdet) hc
  exact heq ▸ (summable_localDensityTerm p A hA hdet).hasSum

/-- The local density is nonnegative because every normalized residue count is. -/
theorem localQuadraticDensity_nonneg (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    0 ≤ localQuadraticDensity p A := by
  apply ge_of_tendsto (tendsto_normalizedPrimePowerZeroCount p A hA hdet)
  exact Filter.Eventually.of_forall fun k => by
    unfold normalizedPrimePowerZeroCount
    positivity

end QuaternaryQuadraticForms
