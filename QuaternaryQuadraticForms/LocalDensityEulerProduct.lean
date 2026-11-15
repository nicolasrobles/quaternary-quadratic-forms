import QuaternaryQuadraticForms.LocalDensityGoodPrime
import QuaternaryQuadraticForms.LocalDensityConvergence
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The corrected local-density Euler product

The source supplies its Dirichlet character and its Legendre values at good
primes. Every bad-prime factor retains that original character and the actual
counting density. The finite exceptional set requires no nonvanishing or
positivity assumption. Absolute summability of the deviations from one proves
convergence of the corrected product and of its norm product.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

/-- The good-prime value of the actual real counting density, viewed in `ℂ`. -/
theorem localQuadraticDensity_goodPrime (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    (localQuadraticDensity p A : ℂ) =
      (1 - (legendreSym p A.det : ℂ) / (p : ℂ) ^ 2) /
        (1 - (legendreSym p A.det : ℂ) / (p : ℂ)) :=
  (hasSum_localDensityTerm p A hA hdet).unique
    (localDensityTerm_hasSum_goodPrime p A hA hp)

/-- The same formula with the manuscript's original supplied character. -/
theorem source_localQuadraticDensity_goodPrime (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    (localQuadraticDensity p A : ℂ) =
      (1 - χ (p : ZMod M) / (p : ℂ) ^ 2) / (1 - χ (p : ZMod M) / (p : ℂ)) := by
  rw [hχ p hp]
  exact localQuadraticDensity_goodPrime p A hA hdet hp

/-- Exactly the corrected factor `(1 - χ(p)/p) σ_p` in source `eq:SF`,
including the original character values at bad primes. -/
def correctedLocalDensityFactor (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (p : Nat.Primes) : ℂ :=
  letI : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩
  (1 - χ ((p : ℕ) : ZMod M) / ((p : ℕ) : ℂ)) *
    (localQuadraticDensity (p : ℕ) A : ℂ)

/-- At a good prime the correction cancels exactly the nonzero geometric
denominator, leaving `1 - χ(p)/p²`. -/
theorem correctedLocalDensityFactor_goodPrime (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (p : Nat.Primes) (hp : ¬(p : ℕ) ∣ quadraticBadPrimeModulus A) :
    correctedLocalDensityFactor M χ A p =
      1 - χ ((p : ℕ) : ZMod M) / ((p : ℕ) : ℂ) ^ 2 := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  have hden : 1 - χ ((p : ℕ) : ZMod M) / ((p : ℕ) : ℂ) ≠ 0 := by
    rw [hχ (p : ℕ) hp]
    intro h
    have heq := (sub_eq_zero.mp h).symm
    have hn := localDensity_goodPrime_ratio_norm_lt_one (p : ℕ) A
    simp [heq] at hn
  unfold correctedLocalDensityFactor
  rw [source_localQuadraticDensity_goodPrime M χ (p : ℕ) A hA hdet hχ hp]
  field_simp

/-- The good-prime corrected factor differs from one by at most `p⁻²`. -/
theorem correctedLocalDensityFactor_sub_one_norm_le (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (p : Nat.Primes) (hp : ¬(p : ℕ) ∣ quadraticBadPrimeModulus A) :
    ‖correctedLocalDensityFactor M χ A p - 1‖ ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  rw [correctedLocalDensityFactor_goodPrime M χ A hA hdet hχ p hp]
  simp only [sub_sub_cancel_left, norm_neg, norm_div, norm_pow, Complex.norm_natCast]
  rw [hχ (p : ℕ) hp]
  exact div_le_div_of_nonneg_right (legendreSym_complex_norm_le_one (p : ℕ) A.det)
    (sq_nonneg _)

/-- Nonsingularity makes the exceptional prime set finite. -/
theorem eventually_prime_not_dvd_quadraticBadPrimeModulus
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0) :
    ∀ᶠ p : Nat.Primes in cofinite, ¬(p : ℕ) ∣ quadraticBadPrimeModulus A := by
  have hfinite : {p : Nat.Primes | (p : ℕ) ∈ (quadraticBadPrimeModulus A).primeFactors}.Finite :=
    (quadraticBadPrimeModulus A).primeFactors.finite_toSet.preimage
      Subtype.coe_injective.injOn
  rw [eventually_cofinite]
  simp only [not_not]
  exact hfinite.subset fun p hp => Nat.mem_primeFactors.mpr
    ⟨p.property, hp, quadraticBadPrimeModulus_ne_zero A hdet⟩

/-- Absolute convergence of the corrected product: the actual deviations
from one are summable over all primes, with every bad factor retained. -/
theorem summable_norm_correctedLocalDensityFactor_sub_one
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ)) :
    Summable (fun p : Nat.Primes => ‖correctedLocalDensityFactor M χ A p - 1‖) := by
  have hsum : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).comp_injective
      Subtype.coe_injective
  apply hsum.of_norm_bounded_eventually
  filter_upwards [eventually_prime_not_dvd_quadraticBadPrimeModulus A hdet] with p hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    correctedLocalDensityFactor_sub_one_norm_le M χ A hA hdet hχ p hp

/-- The product in `eq:SF` exists, including any finite zero bad-prime factor. -/
theorem multipliable_correctedLocalDensityFactor
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ)) :
    Multipliable (correctedLocalDensityFactor M χ A) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_correctedLocalDensityFactor_sub_one M χ A hA hdet hχ)
  exact h.congr fun p => by ring

/-- The product of the norms of the actual corrected factors also converges. -/
theorem multipliable_norm_correctedLocalDensityFactor
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ)) :
    Multipliable (fun p : Nat.Primes => ‖correctedLocalDensityFactor M χ A p‖) :=
  (multipliable_correctedLocalDensityFactor M χ A hA hdet hχ).norm

end QuaternaryQuadraticForms
