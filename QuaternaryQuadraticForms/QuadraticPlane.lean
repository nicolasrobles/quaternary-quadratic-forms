import QuaternaryQuadraticForms.MatrixPolynomial
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Tactic.Ring

/-!
# The nondegenerate plane section

The hyperplane is the literal kernel of `x ↦ u · x`. Its quadratic form
is the restriction of the matrix bilinear form. The adjugate identifies it
as the orthogonal complement of a nonisotropic vector.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open LinearMap Matrix Module

variable {K : Type*} [Field K]

/-- The actual linear hyperplane in four coordinates. -/
def planeSubspace (u : Fin 4 → K) : Submodule K (Fin 4 → K) :=
  LinearMap.ker (dotProductBilin K K u)

@[simp] theorem mem_planeSubspace (u x : Fin 4 → K) :
    x ∈ planeSubspace u ↔ dotProduct u x = 0 := Iff.rfl

/-- A symmetric matrix gives a symmetric bilinear form. -/
theorem matrixBilin_isSymm (A : Matrix (Fin 4) (Fin 4) K) (hA : Aᵀ = A) :
    A.toBilin'.IsSymm := by
  constructor
  intro x y
  simp only [Matrix.toBilin'_apply']
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

/-- Multiplication by the matrix cancels its adjugate up to the determinant. -/
theorem matrix_mulVec_adjugate (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K) :
    A.mulVec (A.adjugate.mulVec u) = A.det • u := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The adjugate normal has nonzero self-pairing under the dual-form hypothesis. -/
theorem adjugate_bilin_self (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K) :
    A.toBilin' (A.adjugate.mulVec u) (A.adjugate.mulVec u) =
      A.det * dotProduct u (A.adjugate.mulVec u) := by
  rw [Matrix.toBilin'_apply', matrix_mulVec_adjugate, dotProduct_smul, smul_eq_mul,
    dotProduct_comm]

/-- The geometric plane is the orthogonal complement of the adjugate normal. -/
theorem planeSubspace_eq_orthogonal (A : Matrix (Fin 4) (Fin 4) K)
    (hA : Aᵀ = A) (hdet : A.det ≠ 0) (u : Fin 4 → K) :
    planeSubspace u = A.toBilin'.orthogonal (K ∙ A.adjugate.mulVec u) := by
  rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  ext x
  change dotProduct u x = 0 ↔ A.toBilin' (A.adjugate.mulVec u) x = 0
  rw [(matrixBilin_isSymm A hA).eq, Matrix.toBilin'_apply', matrix_mulVec_adjugate,
    dotProduct_smul, smul_eq_mul, dotProduct_comm]
  simp [hdet]

/-- The restriction to the plane section is nondegenerate. -/
theorem plane_bilin_nondegenerate (A : Matrix (Fin 4) (Fin 4) K)
    (hA : Aᵀ = A) (hdet : A.det ≠ 0) (u : Fin 4 → K)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0) :
    (A.toBilin'.restrict (planeSubspace u)).Nondegenerate := by
  rw [planeSubspace_eq_orthogonal A hA hdet u]
  apply LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
    A.toBilin' (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet)
    (matrixBilin_isSymm A hA).isRefl
  change A.toBilin' (A.adjugate.mulVec u) (A.adjugate.mulVec u) ≠ 0
  rw [adjugate_bilin_self]
  exact mul_ne_zero hdet hu

/-- The dual-form hypothesis makes the hyperplane functional nonzero. -/
theorem planeFunctional_ne_zero (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0) :
    dotProductBilin K K u ≠ 0 := by
  intro h
  apply hu
  exact LinearMap.congr_fun h (A.adjugate.mulVec u)

/-- A nonzero hyperplane in four-space has dimension three. -/
theorem planeSubspace_finrank (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0) :
    Module.finrank K (planeSubspace u) = 3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (planeFunctional_ne_zero A u hu)
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  change Module.finrank K (planeSubspace u) + 1 = 4 at h
  omega

/-- The linear polynomial defining the plane. -/
def planePolynomial (u : Fin 4 → K) : MvPolynomial (Fin 4) K :=
  ∑ i, MvPolynomial.C (u i) * MvPolynomial.X i

theorem eval_planePolynomial (u x : Fin 4 → K) :
    MvPolynomial.eval x (planePolynomial u) = dotProduct u x := by
  simp [planePolynomial, dotProduct]

theorem planePolynomial_totalDegree_le (u : Fin 4 → K) :
    (planePolynomial u).totalDegree ≤ 1 := by
  have h : (planePolynomial u).IsHomogeneous 1 := by
    unfold planePolynomial
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact MvPolynomial.isHomogeneous_C_mul_X (u i) i
  exact h.totalDegree_le

/-- Chevalley--Warning produces an actual nonzero isotropic point in every
four-variable quadratic hyperplane section over a prime field. -/
theorem plane_exists_isotropic (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p) :
    ∃ x : Fin 4 → ZMod p, x ≠ 0 ∧
      dotProduct x (A.mulVec x) = 0 ∧ dotProduct u x = 0 := by
  classical
  have hdegree : (matrixQuadraticPolynomial A).totalDegree +
      (planePolynomial u).totalDegree < Fintype.card (Fin 4) := by
    have hF := matrixQuadraticPolynomial_totalDegree_le A
    have hL := planePolynomial_totalDegree_le u
    simp only [Fintype.card_fin]
    omega
  have hdiv := char_dvd_card_solutions_of_add_lt p hdegree
  by_contra h
  have hz : ∀ x : Fin 4 → ZMod p,
      MvPolynomial.eval x (matrixQuadraticPolynomial A) = 0 ∧
      MvPolynomial.eval x (planePolynomial u) = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    exact h ⟨x, hx0, by simpa [eval_matrixQuadraticPolynomial] using hx.1,
      by simpa [eval_planePolynomial] using hx.2⟩
  letI : Unique {x : Fin 4 → ZMod p //
      MvPolynomial.eval x (matrixQuadraticPolynomial A) = 0 ∧
      MvPolynomial.eval x (planePolynomial u) = 0} :=
    { default := ⟨0, by
        constructor
        · rw [eval_matrixQuadraticPolynomial]; simp
        · rw [eval_planePolynomial]; simp⟩
      uniq := fun x => Subtype.ext (hz x x.property) }
  have hp1 : p ∣ 1 := by simpa using hdiv
  exact (Fact.out : p.Prime).not_dvd_one hp1

end QuaternaryQuadraticForms
