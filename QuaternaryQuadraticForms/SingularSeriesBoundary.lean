import QuaternaryQuadraticForms.SingularSeriesEulerComparison
import QuaternaryQuadraticForms.SingularSeriesConvergence
import QuaternaryQuadraticForms.SingularSeriesConstant
import QuaternaryQuadraticForms.SingularEulerOrdered

/-!
# The boundary identity for the ordered singular series

The equality in the absolutely convergent half-plane is passed to the
boundary using continuity of the actual ordered series, the original
nonprincipal character's analytic L-function, and the finite local
correction. The zero-shift corrected product is identified by uniqueness
of its convergent Euler product.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

/-- At the boundary the finite correction is precisely the corrected
density product with the good factors at divisors of `q` removed. -/
theorem singularSeriesEulerCorrection_zero
    (q M : ℕ) [NeZero q] [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (hq : q.Coprime (quadraticBadPrimeModulus A)) :
    singularSeriesEulerCorrection q M χ A 0 =
      (∏' p : Nat.Primes, correctedLocalDensityFactor M χ A p) *
        singularSeriesRemovalFactor q A := by
  apply (hasProd_restrictedCorrectedShiftedFactor q M χ A hA hdet hχ 0 le_rfl).unique
  apply (hasProd_removedCorrectedLocalDensityFactor M χ A hA hdet hχ q
    (Nat.pos_of_ne_zero (NeZero.ne q)) hq).congr_fun
  intro p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  simp only [restrictedCorrectedShiftedFactor, add_zero,
    shiftedLocalDensity_zero (p : ℕ) A hA hdet,
    correctedLocalDensityFactor_eq_dirichletRealEulerFactor]

/-- The actual ordered value is the manuscript's singular-series constant
times the exact finite reciprocal-density product. -/
theorem singularSeriesValue_zero_eq
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A)) :
    singularSeriesValue q A 0 =
      singularSeriesConstant M χ A * singularSeriesRemovalFactor q A := by
  have hnonprincipal : χ ≠ 1 :=
    sourceDirichletCharacter_ne_one A.det hdet hns M χ hχ
  have hL : Continuous (fun z : ℝ => χ.LFunction (↑(1 + z) : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hnonprincipal).continuous.comp
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
  have hleft : Tendsto (singularSeriesValue q A) (𝓝[Set.Ioi 0] 0)
      (𝓝 (singularSeriesValue q A 0)) :=
    (continuousWithinAt_singularSeriesValue_zero A hA hdet hns q hq).mono
      Set.Ioi_subset_Ici_self
  have hright : Tendsto
      (fun z : ℝ => χ.LFunction (↑(1 + z) : ℂ) * singularSeriesEulerCorrection q M χ A z)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (χ.LFunction 1 * singularSeriesEulerCorrection q M χ A 0)) := by
    simpa only [ContinuousWithinAt, add_zero, Complex.ofReal_one] using hL.continuousWithinAt.mul
      ((continuousWithinAt_singularSeriesEulerCorrection_zero q M χ A hA hdet).mono
        Set.Ioi_subset_Ici_self)
  have heq : (singularSeriesValue q A) =ᶠ[𝓝[Set.Ioi 0] 0]
      (fun z : ℝ => χ.LFunction (↑(1 + z) : ℂ) * singularSeriesEulerCorrection q M χ A z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [singularSeriesValue_eq_tsum q A hA hdet z hz]
    exact tsum_singularSeriesTerm_eq_LFunction_mul_correction q M χ A hA hdet hχ z hz
  have hvalue := tendsto_nhds_unique hleft (hright.congr' heq.symm)
  rw [hvalue, singularSeriesEulerCorrection_zero q M χ A hA hdet hχ hq,
    singularSeriesConstant, mul_assoc]

end QuaternaryQuadraticForms
