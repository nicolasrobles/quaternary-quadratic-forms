import QuaternaryQuadraticForms.IntegralGaussSums
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Constants in the uniform quadratic Gauss bound

The determinant of twice the actual quaternary matrix supplies the factor
sixteen in the squared norm, and taking the nonnegative square root supplies
exactly the source constant four. The actual residue unit group has at most
as many elements as the residue ring, including at modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Doubling every entry of a quaternary matrix multiplies its determinant by sixteen. -/
theorem quaternary_det_two_smul (A : Matrix (Fin 4) (Fin 4) ℤ) :
    ((2 : ℤ) • A).det = 16 * A.det := by
  rw [Matrix.det_smul]
  norm_num

/-- The exact absolute determinant used to count the source residue kernel. -/
theorem quaternary_det_two_smul_natAbs (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (((2 : ℤ) • A).det).natAbs = 16 * A.det.natAbs := by
  rw [quaternary_det_two_smul, Int.natAbs_mul]
  norm_num

/-- The squared Gauss estimate gives the exact factor four after taking square roots. -/
theorem gauss_norm_le_of_sq_le (V : ℂ) (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hV : ‖V‖ ^ 2 ≤ (n : ℝ) ^ 4 * (16 * D)) :
    ‖V‖ ≤ 4 * Real.sqrt D * (n : ℝ) ^ 2 := by
  have hnonneg : 0 ≤ 4 * Real.sqrt D * (n : ℝ) ^ 2 := by positivity
  have hsquare : (4 * Real.sqrt D * (n : ℝ) ^ 2) ^ 2 =
      (n : ℝ) ^ 4 * (16 * D) := by
    calc
      _ = (Real.sqrt D) ^ 2 * (16 * (n : ℝ) ^ 4) := by ring
      _ = D * (16 * (n : ℝ) ^ 4) := by rw [Real.sq_sqrt hD]
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg V) hnonneg).mp (hV.trans_eq hsquare.symm)

/-- The actual unit parameters form a subset of the residue ring at every positive modulus. -/
theorem zmod_card_units_le (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ ≤ n := by
  simpa only [ZMod.card] using
    (Fintype.card_le_of_injective (fun a : (ZMod n)ˣ => (a : ZMod n))
      Units.val_injective)

end QuaternaryQuadraticForms
