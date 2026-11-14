import QuaternaryQuadraticForms.MatrixResidueKernel
import QuaternaryQuadraticForms.GoodPrime

/-!
# The doubled integral matrix and its residue kernel

The kernel selected by quadratic polarization is exactly the actual residue
kernel of the integer matrix `2 • A`. These identities impose no restriction
on the modulus or on the reduction of the determinant.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Coefficient reduction commutes with doubling the actual integer matrix. -/
theorem reduceQuadraticMatrix_two_smul (n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    reduceQuadraticMatrix n ((2 : ℤ) • A) =
      (2 : ZMod n) • reduceQuadraticMatrix n A := by
  ext i j
  change ((2 * A i j : ℤ) : ZMod n) = (2 : ZMod n) * (A i j : ZMod n)
  push_cast
  rfl

/-- The finite set selected by polarization is the kernel of the doubled integer matrix. -/
theorem matrixResidueKernel_two_smul (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    matrixResidueKernel n ((2 : ℤ) • A) =
      Finset.univ.filter (fun z : Fin 4 → ZMod n =>
        (2 : ZMod n) • (reduceQuadraticMatrix n A).mulVec z = 0) := by
  classical
  ext z
  simp only [mem_matrixResidueKernel, Finset.mem_filter, Finset.mem_univ, true_and]
  change (reduceQuadraticMatrix n ((2 : ℤ) • A)).mulVec z = 0 ↔ _
  rw [reduceQuadraticMatrix_two_smul, Matrix.smul_mulVec]

end QuaternaryQuadraticForms
