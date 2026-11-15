import QuaternaryQuadraticForms.SingularSeriesPrimeSets
import QuaternaryQuadraticForms.SingularSeriesLFactors
import QuaternaryQuadraticForms.ShiftedLocalGoodPrime
import QuaternaryQuadraticForms.LocalDensityEulerProduct

/-!
# The source singular-series constant and finite removal of good primes

The singular-series constant retains the original character and every actual
local counting density. A coprime modulus removes only good primes, whose
densities have already been proved nonzero. No exceptional local density and
no complete singular-series constant is ever inverted.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The source constant `L(1, χ)` times its actual corrected density product. -/
def singularSeriesConstant (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) : ℂ :=
  χ.LFunction 1 * ∏' p : Nat.Primes, correctedLocalDensityFactor M χ A p

/-- The finite product of reciprocal local densities at prime divisors of the
modulus. Its use is justified below only when the modulus is good. -/
def singularSeriesRemovalFactor (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) : ℂ :=
  ∏ p ∈ singularSeriesPrimeDivisors q,
    letI : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩
    (localQuadraticDensity (p : ℕ) A : ℂ)⁻¹

/-- The corrected density factor is the original character's exponent-one
Euler factor times the actual local density. -/
theorem correctedLocalDensityFactor_eq_dirichletRealEulerFactor
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (p : Nat.Primes) :
    correctedLocalDensityFactor M χ A p =
      dirichletRealEulerFactor M χ p 1 *
        (@localQuadraticDensity (p : ℕ) ⟨p.property.ne_zero⟩ A : ℂ) := by
  simp only [correctedLocalDensityFactor, dirichletRealEulerFactor,
    Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]

/-- A good prime has nonzero actual density; this is a consequence of its
explicit formula, not an additional local-solubility premise. -/
theorem localQuadraticDensity_goodPrime_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hp : ¬p ∣ quadraticBadPrimeModulus A) :
    (localQuadraticDensity p A : ℂ) ≠ 0 := by
  simpa only [shiftedLocalDensity_zero p A hA hdet] using
    shiftedLocalDensity_goodPrime_ne_zero p A hA hp 0 (le_refl 0)

/-- Removing the Euler factors at primes dividing a good modulus multiplies
the corrected density product by exactly the reciprocal good densities. -/
theorem hasProd_removedCorrectedLocalDensityFactor
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (q : ℕ) (hq : 0 < q) (hqgood : q.Coprime (quadraticBadPrimeModulus A)) :
    HasProd (fun p : Nat.Primes =>
      if (p : ℕ) ∣ q then dirichletRealEulerFactor M χ p 1
      else correctedLocalDensityFactor M χ A p)
      ((∏' p : Nat.Primes, correctedLocalDensityFactor M χ A p) *
        singularSeriesRemovalFactor q A) := by
  classical
  let s := singularSeriesPrimeDivisors q
  let g : Nat.Primes → ℂ := fun p =>
    if (p : ℕ) ∣ q then dirichletRealEulerFactor M χ p 1
    else correctedLocalDensityFactor M χ A p
  have hmem (p : Nat.Primes) : p ∈ s ↔ (p : ℕ) ∣ q :=
    mem_singularSeriesPrimeDivisors q hq.ne' p
  have hgood (p : Nat.Primes) (hp : p ∈ s) :
      ¬(p : ℕ) ∣ quadraticBadPrimeModulus A :=
    p.property.coprime_iff_not_dvd.mp (hqgood.of_dvd_left ((hmem p).mp hp))
  have hnz (p : Nat.Primes) (hp : p ∈ s) :
      correctedLocalDensityFactor M χ A p ≠ 0 := by
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    rw [correctedLocalDensityFactor_eq_dirichletRealEulerFactor]
    exact mul_ne_zero (dirichletRealEulerFactor_ne_zero M χ p 1 (le_refl 1))
      (localQuadraticDensity_goodPrime_ne_zero (p : ℕ) A hA hdet (hgood p hp))
  have heq (p : Nat.Primes) (hp : p ∉ s) :
      correctedLocalDensityFactor M χ A p = g p := by
    simp only [g, if_neg (mt (hmem p).mpr hp)]
  have hprod :=
    (multipliable_correctedLocalDensityFactor M χ A hA hdet hχ).hasProd.congr_cofinite₀
      hnz heq
  have hratio : (∏ p ∈ s, g p) / (∏ p ∈ s, correctedLocalDensityFactor M χ A p) =
      singularSeriesRemovalFactor q A := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [show g p = dirichletRealEulerFactor M χ p 1 by
      simp only [g, if_pos ((hmem p).mp hp)],
      correctedLocalDensityFactor_eq_dirichletRealEulerFactor,
      ← div_div, div_self (dirichletRealEulerFactor_ne_zero M χ p 1 (le_refl 1)),
      one_div]
  simpa only [hratio] using hprod

end QuaternaryQuadraticForms
