import QuaternaryQuadraticForms.GaussBoundConstants

/-!
# Passing from the actual Gauss bounds to the complete sum

The triangle inequality is applied to the existing unit-parameter sum.
The inner bound remains explicit in this composition helper and is proved
from the source matrix hypotheses in the final uniform estimate.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A common norm bound on the actual inner Gauss sums gives the corresponding
bound for the manuscript's complete sum, at every positive modulus. -/
theorem unweightedCompleteSum_norm_le_of_gauss_bound (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (K : ℝ)
    (hK : ∀ a : (ZMod n)ˣ,
      ‖quadraticGaussSum n (A.map (Int.castRingHom (ZMod n))) (a : ZMod n)
        (fun i => (u i : ZMod n))‖ ≤ K) :
    ‖unweightedCompleteSum n A u‖ ≤ (n : ℝ) * K := by
  have hKnonneg : 0 ≤ K := (norm_nonneg _).trans (hK 1)
  rw [unweightedCompleteSum_eq_sum_quadraticGaussSum]
  calc
    _ ≤ ∑ a : (ZMod n)ˣ,
        ‖quadraticGaussSum n (A.map (Int.castRingHom (ZMod n))) (a : ZMod n)
          (fun i => (u i : ZMod n))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod n)ˣ, K := Finset.sum_le_sum (fun a _ => hK a)
    _ = (Fintype.card (ZMod n)ˣ : ℝ) * K := by simp
    _ ≤ (n : ℝ) * K := by
      apply mul_le_mul_of_nonneg_right _ hKnonneg
      exact_mod_cast zmod_card_units_le n

end QuaternaryQuadraticForms
