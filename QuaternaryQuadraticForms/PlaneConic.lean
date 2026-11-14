import QuaternaryQuadraticForms.TransversePullback
import QuaternaryQuadraticForms.ProjectiveRays

/-!
# The actual projective plane section and its parametrization data

This record states the properties to be proved for the coordinate forms.
Its projective equivalence is tied to literal polynomial evaluation on every
nonzero representative, and its tangent vectors are actual formal partials.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- The literal projective zero set of the quadratic form in the given plane. -/
def PlaneConicPoints (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K) :=
  {P : ℙ K (Fin 4 → K) //
    dotProduct P.rep (A.mulVec P.rep) = 0 ∧ dotProduct u P.rep = 0}

/-- The proved properties of the actual binary quadratic coordinate forms.
This is data to construct, not an external mathematical premise. -/
structure ParametrizedPlaneSection (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (μ : Fin 4 → MvPolynomial (Fin 2) K) where
  homogeneous : ∀ i, (μ i).IsHomogeneous 2
  nonzero : ∀ v : Fin 2 → K, v ≠ 0 → polynomialVectorEval μ v ≠ 0
  pointEquiv : ℙ K (Fin 2 → K) ≃ PlaneConicPoints A u
  pointEquiv_mk : ∀ (v : Fin 2 → K) (hv : v ≠ 0),
    (pointEquiv (Projectivization.mk K v hv)).val =
      Projectivization.mk K (polynomialVectorEval μ v) (nonzero v hv)
  partials : ∀ v : Fin 2 → K, v ≠ 0 →
    LinearIndependent K (fun i : Fin 2 => polynomialVectorDerivative μ i v)
  quadric_identity : MvPolynomial.aeval μ (matrixQuadraticPolynomial A) = 0
  plane_identity : MvPolynomial.aeval μ (planePolynomial u) = 0

end QuaternaryQuadraticForms
