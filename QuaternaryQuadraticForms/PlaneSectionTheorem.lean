import QuaternaryQuadraticForms.ConicParametrization
import QuaternaryQuadraticForms.PlaneSectionBound
import QuaternaryQuadraticForms.TransversalityRank

/-!
# The manuscript's plane-section estimate

The parametrization is constructed from the good-prime and dual-form
hypotheses. The source's literal rank-three condition is then converted to
the gradient independence used in the proof of the pulled-back Weil bound.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Lemma 4.3 over the prime field, with the actual geometric matrix-rank
condition and with the required parametrizations constructed in the proof. -/
theorem plane_section_bound_prime_field (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : PlaneTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)) :
    ‖projectiveSectionTrace A ψ G u‖ ≤ (2 * (n : ℝ) - 1) * Real.sqrt p + 1 := by
  obtain ⟨μ, _, hall⟩ := conic_parametrization_prime_field.{0} p hp A hA hdet u hu
  have hbase : Nonempty (ParametrizedPlaneSection A u μ) := by
    simpa [MvPolynomial.map_id] using hall (ZMod p)
  obtain ⟨c⟩ := hbase
  obtain ⟨cgeom⟩ := hall (AlgebraicClosure (ZMod p))
  exact plane_section_bound_of_parametrization p A u μ c cgeom ψ hψ hG hn horder
    ((planeTransverseRank_iff _ _ _).mp htrans)

/-- Lemma 4.3 for the original integral matrix and the exact good-prime
condition `p ∤ 2 |det A|`. The sum is the manuscript's literal section trace. -/
theorem plane_section_bound (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ZMod p)
    (hu : dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : PlaneTransverseRank
      ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)) :
    ‖projectiveSectionTrace (reduceQuadraticMatrix p A) ψ G u‖ ≤
      (2 * (n : ℝ) - 1) * Real.sqrt p + 1 :=
  plane_section_bound_prime_field p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) u hu ψ hψ hG hn horder htrans

end QuaternaryQuadraticForms
