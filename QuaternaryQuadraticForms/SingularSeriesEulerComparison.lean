import QuaternaryQuadraticForms.SingularSeriesLFactors
import QuaternaryQuadraticForms.ShiftedLocalGoodPrime
import QuaternaryQuadraticForms.SingularSeriesPrimeSets
import QuaternaryQuadraticForms.SingularEulerProduct

/-!
# Comparing the actual Euler product with the original L-functions

After multiplication by the exponent-one character factor, every good
local factor equals the exponent-two character factor. The remaining
correction is over the finite primes dividing `q N_F`. Its denominators
are character Euler factors, all proved nonzero. Bad local densities are
never divided out.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

/-- The corrected shifted factor with the primes of `q` removed. -/
def restrictedCorrectedShiftedFactor (q M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (p : Nat.Primes) : ℂ :=
  letI : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩
  if (p : ℕ) ∣ q then dirichletRealEulerFactor M χ p (1 + z)
  else dirichletRealEulerFactor M χ p (1 + z) * shiftedLocalDensity (p : ℕ) A z

/-- The finite correction to the absolutely convergent exponent-two
character product. -/
def singularSeriesEulerCorrection (q M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) : ℂ :=
  (χ.LFunction (↑(2 + z) : ℂ))⁻¹ *
    ∏ p ∈ singularSeriesPrimeDivisors (q * quadraticBadPrimeModulus A),
      restrictedCorrectedShiftedFactor q M χ A z p / dirichletRealEulerFactor M χ p (2 + z)

/-- Outside the finite exceptional set the corrected factor is exactly
the exponent-two Euler factor of the original character. -/
theorem restrictedCorrectedShiftedFactor_goodPrime
    (q M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (p : Nat.Primes) (hpq : ¬(p : ℕ) ∣ q)
    (hpN : ¬(p : ℕ) ∣ quadraticBadPrimeModulus A) (z : ℝ) (hz : 0 ≤ z) :
    restrictedCorrectedShiftedFactor q M χ A z p =
      dirichletRealEulerFactor M χ p (2 + z) := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  rw [restrictedCorrectedShiftedFactor, if_neg hpq,
    source_shiftedLocalDensity_goodPrime M χ (p : ℕ) A hA hχ hpN z hz]
  rw [← dirichletRealEulerFactor_eq_div M χ p (1 + z),
    ← dirichletRealEulerFactor_eq_div M χ p (2 + z)]
  exact mul_div_cancel₀ _ (dirichletRealEulerFactor_ne_zero M χ p (1 + z) (by linarith))

/-- The corrected product has an explicit finite correction for every
nonnegative shift, including the boundary zero. -/
theorem hasProd_restrictedCorrectedShiftedFactor
    (q M : ℕ) [NeZero q] [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (z : ℝ) (hz : 0 ≤ z) :
    HasProd (restrictedCorrectedShiftedFactor q M χ A z)
      (singularSeriesEulerCorrection q M χ A z) := by
  have hbase := hasProd_dirichletRealEulerFactor M χ (2 + z) (by linarith)
  have hqN : q * quadraticBadPrimeModulus A ≠ 0 :=
    mul_ne_zero (NeZero.ne q) (quadraticBadPrimeModulus_ne_zero A hdet)
  have hprod := hbase.congr_cofinite₀
    (g := restrictedCorrectedShiftedFactor q M χ A z)
    (s := singularSeriesPrimeDivisors (q * quadraticBadPrimeModulus A))
    (fun p _ => dirichletRealEulerFactor_ne_zero M χ p (2 + z) (by linarith))
    (fun p hp => ?_)
  · simpa only [singularSeriesEulerCorrection, Finset.prod_div_distrib] using hprod
  · have hp' : ¬(p : ℕ) ∣ q * quadraticBadPrimeModulus A := by
      simpa only [mem_singularSeriesPrimeDivisors _ hqN] using hp
    exact (restrictedCorrectedShiftedFactor_goodPrime q M χ A hA hχ p
      (fun h => hp' (dvd_mul_of_dvd_left h _))
      (fun h => hp' (dvd_mul_of_dvd_right h _)) z hz).symm

/-- Absolute convergence identifies the actual shifted series with the
L-function times its finite correction. -/
theorem tsum_singularSeriesTerm_eq_LFunction_mul_correction
    (q M : ℕ) [NeZero q] [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (z : ℝ) (hz : 0 < z) :
    (∑' c : ℕ, singularSeriesTerm q A z c) =
      χ.LFunction (↑(1 + z) : ℂ) * singularSeriesEulerCorrection q M χ A z := by
  have hprod := (hasProd_inv_dirichletRealEulerFactor M χ (1 + z) (by linarith)).mul
    (hasProd_restrictedCorrectedShiftedFactor q M χ A hA hdet hχ z hz.le)
  apply (singularSeries_eulerProduct_hasProd q A hA hdet z hz).unique
  apply hprod.congr_fun
  intro p
  have hf := dirichletRealEulerFactor_ne_zero M χ p (1 + z) (by linarith)
  dsimp only [restrictedCorrectedShiftedFactor]
  by_cases hp : (p : ℕ) ∣ q
  · simp [hp, hf]
  · simp [hp, hf]

/-- The finite Euler correction is continuous from the right at zero. -/
theorem continuousWithinAt_singularSeriesEulerCorrection_zero
    (q M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    ContinuousWithinAt (singularSeriesEulerCorrection q M χ A) (Set.Ici 0) 0 := by
  classical
  unfold singularSeriesEulerCorrection
  apply ContinuousWithinAt.mul
  · apply ContinuousWithinAt.inv₀
    · apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.comp (f := fun z : ℝ => (↑(2 + z) : ℂ))
        (χ.differentiableAt_LFunction (↑(2 + (0 : ℝ)) : ℂ)
          (Or.inl (by norm_num))).continuousAt
      fun_prop
    · simpa using LFunction_real_ne_zero M χ 2 (by norm_num)
  · apply tendsto_finset_prod
    intro p _
    apply ContinuousWithinAt.div
    · have hf : Continuous (fun z : ℝ => dirichletRealEulerFactor M χ p (1 + z)) :=
        (continuous_dirichletRealEulerFactor M χ p).comp (continuous_const.add continuous_id)
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      unfold restrictedCorrectedShiftedFactor
      split_ifs
      · exact hf.continuousWithinAt
      · exact hf.continuousWithinAt.mul
          ((continuousOn_shiftedLocalDensity (p : ℕ) A hA hdet) 0 (by simp))
    · exact ((continuous_dirichletRealEulerFactor M χ p).comp
        (continuous_const.add continuous_id)).continuousWithinAt
    · exact dirichletRealEulerFactor_ne_zero M χ p (2 + 0) (by norm_num)

end QuaternaryQuadraticForms
