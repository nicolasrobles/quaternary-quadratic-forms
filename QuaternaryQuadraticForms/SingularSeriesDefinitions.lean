import QuaternaryQuadraticForms.ModulusSumFactorization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual ordered singular series

The coefficient uses the manuscript's complete sum and literal coprimality
restriction. The cutoff is real. At the boundary shift zero the value is
defined by the ordered partial sums, without asserting unconditional
summability of the coefficients.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual complete-sum coefficient with the coprimality restriction. -/
def coprimeCompleteSumValue (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (c : ℕ) : ℂ :=
  if c.Coprime q then unweightedCompleteSumValue c A 0 else 0

/-- The shifted actual singular-series summand. -/
def singularSeriesTerm (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : ℝ) (c : ℕ) : ℂ :=
  coprimeCompleteSumValue q A c / (↑((c : ℝ) ^ (4 + z)) : ℂ)

/-- Increasing-modulus partial sums at an arbitrary real cutoff. -/
def singularSeriesPartialSum (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z X : ℝ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 ⌊X⌋₊, singularSeriesTerm q A z c

/-- The ordered value; convergence is proved separately from this definition. -/
def singularSeriesValue (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : ℝ) : ℂ :=
  limUnder Filter.atTop (singularSeriesPartialSum q A z)

/-- The total coefficient is zero at the excluded modulus zero. -/
theorem coprimeCompleteSumValue_zero (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    coprimeCompleteSumValue q A 0 = 0 := by
  simp [coprimeCompleteSumValue, unweightedCompleteSumValue]

/-- The shifted summand also vanishes at zero. -/
theorem singularSeriesTerm_zero (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : ℝ) : singularSeriesTerm q A z 0 = 0 := by
  simp [singularSeriesTerm, coprimeCompleteSumValue_zero]

/-- The literal restricted partial coefficient sum is the one in Lemma 3.7. -/
theorem sum_coprimeCompleteSumValue (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (X : ℝ) :
    (∑ c ∈ Finset.Icc 1 ⌊X⌋₊, coprimeCompleteSumValue q A c) =
      unweightedModulusSum q 1 A 0 X := by
  simp only [coprimeCompleteSumValue, unweightedModulusSum, gcdModuliUpTo,
    Finset.sum_filter, Nat.Coprime]

/-- At shift zero the denominator is the ordinary fourth power. -/
theorem singularSeriesTerm_at_zero (q : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (c : ℕ) :
    singularSeriesTerm q A 0 c = coprimeCompleteSumValue q A c / (c : ℂ) ^ 4 := by
  simp [singularSeriesTerm]

end QuaternaryQuadraticForms
