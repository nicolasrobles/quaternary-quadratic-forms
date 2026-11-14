import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The actual residue kernel of an integral matrix

The finite set below consists of all four-coordinate residue vectors killed by
the entrywise reduction of the given integer matrix. No invertibility of the
matrix modulo the modulus is imposed.
-/

namespace QuaternaryQuadraticForms

noncomputable def matrixResidueKernel (n : ℕ) [NeZero n]
    (B : Matrix (Fin 4) (Fin 4) ℤ) : Finset (Fin 4 → ZMod n) := by
  classical
  exact Finset.univ.filter fun z =>
    (B.map (Int.castRingHom (ZMod n))).mulVec z = 0

@[simp] theorem mem_matrixResidueKernel (n : ℕ) [NeZero n]
    (B : Matrix (Fin 4) (Fin 4) ℤ) (z : Fin 4 → ZMod n) :
    z ∈ matrixResidueKernel n B ↔
      (B.map (Int.castRingHom (ZMod n))).mulVec z = 0 := by
  classical
  simp [matrixResidueKernel]

end QuaternaryQuadraticForms
