import QuaternaryQuadraticForms.MatrixResidueKernel
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index

/-! # Determinant bound for the actual residue kernel

The range of a nonsingular integer matrix has index equal to the absolute
determinant. Coordinate reduction is surjective and carries that range onto
the range of the actual residue matrix. Its index therefore divides the
integer index. For a finite endomorphism, the range index is the cardinality
of its kernel. This proves the desired bound at every positive modulus,
including modulus one, without a modular invertibility assumption.
-/

namespace QuaternaryQuadraticForms

private def integerVectorReduction (n : ℕ) :
    (Fin 4 → ℤ) →+ (Fin 4 → ZMod n) where
  toFun x i := (x i : ZMod n)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

private theorem integerVectorReduction_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (integerVectorReduction n) := by
  intro z
  refine ⟨fun i => ((z i).val : ℤ), ?_⟩
  ext i
  simp [integerVectorReduction]

private theorem integerMatrix_reduction_commutes (n : ℕ)
    (B : Matrix (Fin 4) (Fin 4) ℤ) :
    (integerVectorReduction n).comp (Matrix.toLin' B).toAddMonoidHom =
      (Matrix.toLin' (B.map (Int.castRingHom (ZMod n)))).toAddMonoidHom.comp
        (integerVectorReduction n) := by
  ext x i
  simp [integerVectorReduction, Matrix.mulVec, dotProduct]

private theorem integerMatrix_reduction_range (n : ℕ) [NeZero n]
    (B : Matrix (Fin 4) (Fin 4) ℤ) :
    (Matrix.toLin' B).toAddMonoidHom.range.map (integerVectorReduction n) =
      (Matrix.toLin' (B.map (Int.castRingHom (ZMod n)))).toAddMonoidHom.range := by
  rw [AddMonoidHom.map_range, integerMatrix_reduction_commutes,
    AddMonoidHom.range_comp,
    (integerVectorReduction n).range_eq_top_of_surjective
      (integerVectorReduction_surjective n), ← AddMonoidHom.range_eq_map]

private theorem integerMatrix_range_index
    (B : Matrix (Fin 4) (Fin 4) ℤ) (hB : B.det ≠ 0) :
    (Matrix.toLin' B).toAddMonoidHom.range.index = B.det.natAbs := by
  let f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' B
  have hdet : f.det ≠ 0 := by
    simpa only [f, LinearMap.det_toLin'] using hB
  have hker : LinearMap.ker f = ⊥ := by
    by_contra hk
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := f)).mpr hk)
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  have h := Submodule.natAbs_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hinj)
  change (LinearMap.det f).natAbs = Nat.card ((Fin 4 → ℤ) ⧸ LinearMap.range f) at h
  change Nat.card ((Fin 4 → ℤ) ⧸ LinearMap.range f) = B.det.natAbs
  simpa only [f, LinearMap.det_toLin'] using h.symm

private theorem matrixResidueKernel_card_eq_ker (n : ℕ) [NeZero n]
    (B : Matrix (Fin 4) (Fin 4) ℤ) :
    (matrixResidueKernel n B).card =
      Nat.card (Matrix.toLin' (B.map (Int.castRingHom (ZMod n)))).toAddMonoidHom.ker := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [matrixResidueKernel, AddMonoidHom.mem_ker]

/-- The actual residue kernel has at most the absolute integer determinant
many elements at every positive modulus. -/
theorem matrixResidueKernel_card_le_det (n : ℕ) [NeZero n]
    (B : Matrix (Fin 4) (Fin 4) ℤ) (hB : B.det ≠ 0) :
    (matrixResidueKernel n B).card ≤ B.det.natAbs := by
  have hdiv := (Matrix.toLin' B).toAddMonoidHom.range.index_map_dvd
    (integerVectorReduction_surjective n)
  rw [integerMatrix_reduction_range, integerMatrix_range_index B hB,
    AddSubgroup.index_range, ← matrixResidueKernel_card_eq_ker] at hdiv
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hB) hdiv

end QuaternaryQuadraticForms
