import QuaternaryQuadraticForms.ScalarExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The quadratic restriction to an arbitrary plane

A nonsingular symmetric quadratic form in four coordinates cannot vanish
identically on a three-dimensional subspace when two is nonzero. Polarization
would make that subspace orthogonal to itself, although its orthogonal
complement has dimension one. We then express the actual restriction in
three linear coordinates as a nonzero polynomial of degree at most two.
-/

noncomputable section

namespace QuaternaryQuadraticForms

variable {K : Type*} [Field K]

/-- The quadratic form takes a nonzero value on every actual hyperplane.
No nonvanishing condition on the dual quadratic form is required. -/
theorem plane_exists_nonzero_quadratic_value
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → K) (hu : u ≠ 0) :
    ∃ x : planeSubspace u, dotProduct x.val (A.mulVec x.val) ≠ 0 := by
  classical
  by_contra! hzero
  have hsym := matrixBilin_isSymm A hA
  have hnd : A.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  have hzeroB (x : planeSubspace u) : A.toBilin' x.val x.val = 0 :=
    (Matrix.toBilin'_apply' A x.val x.val).trans (hzero x)
  have hpair (x y : planeSubspace u) : A.toBilin' x.val y.val = 0 := by
    have hxy := hzeroB (x + y)
    change A.toBilin' (x.val + y.val) (x.val + y.val) = 0 at hxy
    simp only [map_add, LinearMap.add_apply] at hxy
    rw [hzeroB x, hzeroB y, hsym.eq y.val x.val] at hxy
    simp only [zero_add, add_zero] at hxy
    have htwo : (2 : K) * A.toBilin' x.val y.val = 0 := by
      simpa only [two_mul] using hxy
    exact (mul_eq_zero.mp htwo).resolve_left h2
  have hle : planeSubspace u ≤ A.toBilin'.orthogonal (planeSubspace u) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hpair ⟨y, hy⟩ ⟨x, hx⟩
  have horth : Module.finrank K (A.toBilin'.orthogonal (planeSubspace u)) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd hsym.isRefl,
      planeSubspace_finrank_of_ne_zero u hu]
    simp
  have hdim := Submodule.finrank_mono hle
  rw [planeSubspace_finrank_of_ne_zero u hu, horth] at hdim
  omega

/-- Three linear coordinates for the literal hyperplane. -/
def planeCoordinateEquiv (u : Fin 4 → K) (hu : u ≠ 0) :
    (Fin 3 → K) ≃ₗ[K] planeSubspace u :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [planeSubspace_finrank_of_ne_zero u hu]
    simp)

/-- The actual ternary polynomial obtained by restricting the matrix quadratic
polynomial along a linear coordinate equivalence of the hyperplane. -/
def planeRestrictionPolynomial
    (A : Matrix (Fin 4) (Fin 4) K) {u : Fin 4 → K}
    (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u) : MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval
    (coordinatePolynomial ((planeSubspace u).subtype.comp e.toLinearMap))
    (matrixQuadraticPolynomial A)

/-- Evaluating the coordinate polynomial is evaluating the original quadratic
form on the corresponding actual vector in the plane. -/
theorem eval_planeRestrictionPolynomial
    (A : Matrix (Fin 4) (Fin 4) K) {u : Fin 4 → K}
    (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u) (y : Fin 3 → K) :
    MvPolynomial.eval y (planeRestrictionPolynomial A e) =
      dotProduct (e y).val (A.mulVec (e y).val) := by
  simp only [planeRestrictionPolynomial, eval_aeval_polynomial,
    eval_coordinatePolynomial, eval_matrixQuadraticPolynomial]
  rfl

/-- Linear coordinate substitution preserves the homogeneous quadratic degree. -/
theorem planeRestrictionPolynomial_homogeneous
    (A : Matrix (Fin 4) (Fin 4) K) {u : Fin 4 → K}
    (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u) :
    (planeRestrictionPolynomial A e).IsHomogeneous 2 := by
  simpa only [planeRestrictionPolynomial, one_mul] using
    (matrixQuadraticPolynomial_homogeneous A).aeval
      (coordinatePolynomial ((planeSubspace u).subtype.comp e.toLinearMap))
      (coordinatePolynomial_homogeneous ((planeSubspace u).subtype.comp e.toLinearMap))

/-- The actual restricted polynomial has total degree at most two. -/
theorem planeRestrictionPolynomial_totalDegree_le
    (A : Matrix (Fin 4) (Fin 4) K) {u : Fin 4 → K}
    (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u) :
    (planeRestrictionPolynomial A e).totalDegree ≤ 2 :=
  (planeRestrictionPolynomial_homogeneous A e).totalDegree_le

/-- The coordinate restriction is not the zero polynomial. Its nonvanishing
is proved using an actual nonzero value, without identifying polynomials
solely from their values on a finite field. -/
theorem planeRestrictionPolynomial_ne_zero
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → K) (hu : u ≠ 0)
    (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u) :
    planeRestrictionPolynomial A e ≠ 0 := by
  obtain ⟨x, hx⟩ := plane_exists_nonzero_quadratic_value A hA hdet h2 u hu
  obtain ⟨y, hy⟩ := e.surjective x
  intro hzero
  have heval : MvPolynomial.eval y (planeRestrictionPolynomial A e) = 0 := by
    rw [hzero, map_zero]
  rw [eval_planeRestrictionPolynomial, hy] at heval
  exact hx heval

/-- A nonzero ternary quadratic with the literal plane-coordinate evaluation
identity, for use in counting the points on every plane section. -/
theorem exists_plane_quadratic_restriction
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → K) (hu : u ≠ 0) :
    ∃ (e : (Fin 3 → K) ≃ₗ[K] planeSubspace u)
      (H : MvPolynomial (Fin 3) K),
      H ≠ 0 ∧ H.totalDegree ≤ 2 ∧
        ∀ y : Fin 3 → K,
          MvPolynomial.eval y H = dotProduct (e y).val (A.mulVec (e y).val) := by
  let e := planeCoordinateEquiv u hu
  exact ⟨e, planeRestrictionPolynomial A e,
    planeRestrictionPolynomial_ne_zero A hA hdet h2 u hu e,
    planeRestrictionPolynomial_totalDegree_le A e, eval_planeRestrictionPolynomial A e⟩

end QuaternaryQuadraticForms
