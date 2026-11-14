import QuaternaryQuadraticForms.TransversePullback
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The literal matrix-rank transversality hypothesis

The manuscript states transversality as rank three of the matrix whose rows
are the two polynomial gradients and the plane normal. This file identifies
that condition with the linear independence used by the tangent-space proof.
-/

namespace QuaternaryQuadraticForms

/-- A three-row matrix over a field has rank three exactly when its rows
are linearly independent. -/
theorem rank_three_iff_linearIndependent {K : Type*} [Field K]
    (v : Fin 3 → Fin 4 → K) :
    Matrix.rank v = 3 ↔ LinearIndependent K v := by
  rw [linearIndependent_iff_card_eq_finrank_span,
    Matrix.rank_eq_finrank_span_row]
  change Module.finrank K (Submodule.span K (Set.range v)) = 3 ↔
    3 = Module.finrank K (Submodule.span K (Set.range v))
  exact eq_comm

/-- The rank condition in the manuscript, using the actual formal gradients
at each nonzero common zero of the two polynomials and the plane equation. -/
def PlaneTransverseRank {K : Type*} [Field K]
    (F G : MvPolynomial (Fin 4) K) (u : Fin 4 → K) : Prop :=
  ∀ x : Fin 4 → K, x ≠ 0 → MvPolynomial.eval x F = 0 →
    MvPolynomial.eval x G = 0 → dotProduct u x = 0 →
      Matrix.rank ![polynomialGradient F x, polynomialGradient G x, u] = 3

/-- The source's matrix-rank formulation and the proof's linear-independence
formulation of transversality are equivalent. -/
theorem planeTransverseRank_iff {K : Type*} [Field K]
    (F G : MvPolynomial (Fin 4) K) (u : Fin 4 → K) :
    PlaneTransverseRank F G u ↔ PlaneTransverse F G u := by
  constructor
  · intro h x hx hF hG hu
    exact (rank_three_iff_linearIndependent _).mp (h x hx hF hG hu)
  · intro h x hx hF hG hu
    exact (rank_three_iff_linearIndependent _).mpr (h x hx hF hG hu)

end QuaternaryQuadraticForms
