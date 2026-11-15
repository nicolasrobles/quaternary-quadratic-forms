import QuaternaryQuadraticForms.CompleteSums
import Mathlib.Data.Real.Archimedean

/-!
# The actual absolute sum over moduli

The cutoff is an arbitrary real number. Positive natural moduli up to
its natural floor are filtered by the source's literal gcd condition.
The zero-modulus extension is used only to make a total summand; zero
never belongs to the summation set.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The positive moduli with the exact gcd restriction in Lemma 3.6. -/
def gcdModuliUpTo (q d T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun c => Nat.gcd c q = d)

/-- The finite summation set retains positivity, the cutoff, and the gcd. -/
theorem mem_gcdModuliUpTo (q d T c : ℕ) :
    c ∈ gcdModuliUpTo q d T ↔ 1 ≤ c ∧ c ≤ T ∧ Nat.gcd c q = d := by
  simp only [gcdModuliUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The actual norm divided by the modulus cubed, extended by zero only
at the excluded zero modulus. -/
def normalizedMixedCompleteSum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (c : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℝ :=
  if hc : c = 0 then 0 else
    letI : NeZero c := ⟨hc⟩
    ‖mixedCompleteSum ξ q c A u‖ / (c : ℝ) ^ 3

/-- At every positive modulus the summand is exactly the source term. -/
theorem normalizedMixedCompleteSum_of_neZero
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    normalizedMixedCompleteSum ξ q c A u =
      ‖mixedCompleteSum ξ q c A u‖ / (c : ℝ) ^ 3 := by
  simp only [normalizedMixedCompleteSum, dif_neg (NeZero.ne c)]

/-- Every summand in the absolute modulus sum is nonnegative. -/
theorem normalizedMixedCompleteSum_nonneg
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (c : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    0 ≤ normalizedMixedCompleteSum ξ q c A u := by
  unfold normalizedMixedCompleteSum
  split_ifs
  · exact le_rfl
  · exact div_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- The literal finite sum in Lemma 3.6, with a real cutoff and exact gcd. -/
def modulusNormSum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (d : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (X : ℝ) : ℝ :=
  ∑ c ∈ gcdModuliUpTo q d ⌊X⌋₊, normalizedMixedCompleteSum ξ q c A u

/-- The actual absolute modulus sum is nonnegative. -/
theorem modulusNormSum_nonneg
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (d : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (X : ℝ) :
    0 ≤ modulusNormSum ξ q d A u X := by
  exact Finset.sum_nonneg (fun c _ => normalizedMixedCompleteSum_nonneg ξ q c A u)

/-- Pointwise vanishing on the actual summation set gives the zero sum. -/
theorem modulusNormSum_eq_zero_of_vanishing
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (d : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (X : ℝ)
    (hz : ∀ c : ℕ, ∀ hc : c ∈ gcdModuliUpTo q d ⌊X⌋₊,
      letI : NeZero c := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
        ((mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc).1)⟩
      mixedCompleteSum ξ q c A u = 0) :
    modulusNormSum ξ q d A u X = 0 := by
  apply Finset.sum_eq_zero
  intro c hc
  letI : NeZero c := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
    ((mem_gcdModuliUpTo q d ⌊X⌋₊ c).mp hc).1)⟩
  rw [normalizedMixedCompleteSum_of_neZero, hz c hc, norm_zero, zero_div]

end QuaternaryQuadraticForms
