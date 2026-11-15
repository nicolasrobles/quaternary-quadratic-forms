import QuaternaryQuadraticForms.SingularSeriesBoundary

/-!
# Complete Lemma 3.9

The final source theorem includes the ordered convergence, the exact
singular-series value, and the uniform real-cutoff remainder. Its positive
constant is chosen before the squarefree good modulus and the cutoff.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped Topology

/-- Ordered convergence to the actual singular-series constant, with a
real cutoff and the literal coprimality restriction on every modulus. -/
theorem tendsto_singularSeriesPartialSum_zero
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A)) :
    Tendsto (singularSeriesPartialSum q A 0) atTop
      (𝓝 (singularSeriesConstant M χ A * singularSeriesRemovalFactor q A)) := by
  rw [← singularSeriesValue_zero_eq M χ A hA hdet hns hχ q hq]
  exact tendsto_singularSeriesPartialSum A hA hdet hns q hq 0 le_rfl

/-- The tail is the ordered limit after deleting the fixed initial partial
sum. This formulation makes no unconditional summability claim. -/
theorem tendsto_singularSeriesTail_zero
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A)) (X : ℝ) :
    Tendsto (fun Y : ℝ => singularSeriesPartialSum q A 0 Y - singularSeriesPartialSum q A 0 X)
      atTop (𝓝 (singularSeriesConstant M χ A * singularSeriesRemovalFactor q A -
        singularSeriesPartialSum q A 0 X)) :=
  (tendsto_singularSeriesPartialSum_zero M χ A hA hdet hns hχ q hq).sub tendsto_const_nhds

/-- The same tail is the literal increasing-modulus interval sum. The
interval-membership bridge identifies its endpoints with `X < c ≤ Y`. -/
theorem tendsto_singularSeriesTail_Ioc
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
      χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ))
    (q : ℕ) [NeZero q] (hq : q.Coprime (quadraticBadPrimeModulus A))
    (X : ℝ) (hX : 1 ≤ X) :
    Tendsto (fun Y : ℝ => ∑ c ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, singularSeriesTerm q A 0 c)
      atTop (𝓝 (singularSeriesConstant M χ A * singularSeriesRemovalFactor q A -
        singularSeriesPartialSum q A 0 X)) := by
  apply (tendsto_singularSeriesTail_zero M χ A hA hdet hns hχ q hq X).congr'
  filter_upwards [eventually_ge_atTop X] with Y hY
  exact singularSeriesPartialSum_sub_eq_sum_Ioc q A 0 X Y hX hY

/-- Complete Lemma 3.9: every clause concerns the actual complete sums,
counting densities, and original character. The constant is uniform in
the supplied character data, the modulus, and every real cutoff at least one. -/
theorem source_singular_series
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ quadraticBadPrimeModulus A →
        χ (ℓ : ZMod M) = (legendreSym ℓ A.det : ℂ)) →
      ∀ (q : ℕ) [NeZero q],
      Squarefree q → q.Coprime (quadraticBadPrimeModulus A) →
      Tendsto (singularSeriesPartialSum q A 0) atTop
        (𝓝 (singularSeriesConstant M χ A * singularSeriesRemovalFactor q A)) ∧
      singularSeriesValue q A 0 =
        singularSeriesConstant M χ A * singularSeriesRemovalFactor q A ∧
      ∀ (X : ℝ), 1 ≤ X →
        ‖singularSeriesConstant M χ A * singularSeriesRemovalFactor q A -
          singularSeriesPartialSum q A 0 X‖ ≤ C * (q : ℝ) ^ ε * X ^ (-1 + ε) := by
  obtain ⟨C, hC, htail⟩ := singularSeries_uniform_tail A hA hdet hns ε hε
  refine ⟨C, hC, ?_⟩
  intro M _ χ hχ q _ _hsq hq
  refine ⟨tendsto_singularSeriesPartialSum_zero M χ A hA hdet hns hχ q hq,
    singularSeriesValue_zero_eq M χ A hA hdet hns hχ q hq, ?_⟩
  intro X hX
  rw [← singularSeriesValue_zero_eq M χ A hA hdet hns hχ q hq]
  exact htail q hq 0 le_rfl X hX

end QuaternaryQuadraticForms
