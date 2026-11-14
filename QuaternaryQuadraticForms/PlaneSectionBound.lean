import QuaternaryQuadraticForms.PlaneConic
import QuaternaryQuadraticForms.ScalarExtension
import QuaternaryQuadraticForms.ProjectiveWeil
import QuaternaryQuadraticForms.FourierRays

/-!
# The character-sum bound on a transverse plane section

The actual projective section trace is transported along the proved conic
parametrization. Transversality and the formal chain rule give distinct
geometric zeros of the binary pullback, to which Corollary 2.6 applies.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

local instance (p : ℕ) [Fact p.Prime] :
    Fintype (ℙ (ZMod p) (Fin 2 → ZMod p)) := Fintype.ofFinite _

local instance (p : ℕ) [Fact p.Prime] :
    Fintype (PrimeProjective p) := Fintype.ofFinite _

local instance {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p) :
    Fintype (PlaneConicPoints A u) := by
  unfold PlaneConicPoints
  exact Fintype.ofFinite _

/-- The filtered section trace is the sum over its actual projective zero subtype. -/
theorem projectiveSectionTrace_eq_sum_conic {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p)
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p)) :
    projectiveSectionTrace A ψ G u =
      ∑ P : PlaneConicPoints A u, polynomialCharacterWeight ψ G P.val.rep := by
  classical
  unfold projectiveSectionTrace
  exact Finset.sum_subtype _ (fun _ => by simp [projectiveQuadric, quadraticValue]) _

/-- The conic parametrization identifies the literal section trace with the
projective-line character sum of the actual substituted polynomial. -/
theorem projectiveSectionTrace_eq_projectiveLine {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p)
    (μ : Fin 4 → MvPolynomial (Fin 2) (ZMod p))
    (c : ParametrizedPlaneSection A u μ)
    (ψ : MulChar (ZMod p) ℂ) {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (horder : ψ ^ n = 1) :
    projectiveSectionTrace A ψ G u =
      projectiveLineCharacterSum p ψ (MvPolynomial.aeval μ G) := by
  classical
  rw [projectiveSectionTrace_eq_sum_conic A u ψ G,
    ← c.pointEquiv.sum_comp (fun P => polynomialCharacterWeight ψ G P.val.rep)]
  unfold projectiveLineCharacterSum
  apply Finset.sum_congr rfl
  intro P _
  have hP := c.pointEquiv_mk P.rep P.rep_nonzero
  rw [P.mk_rep] at hP
  rw [hP, projectiveWeight_rep_mk ψ hG horder]
  simp only [polynomialCharacterWeight, eval_aeval_polynomial]
  rfl

/-- Lemma 4.3 after the conic parametrizations have been constructed over the
prime field and its algebraic closure. All simple-root conditions are deductions. -/
theorem plane_section_bound_of_parametrization (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p)
    (μ : Fin 4 → MvPolynomial (Fin 2) (ZMod p))
    (c : ParametrizedPlaneSection A u μ)
    (cgeom : ParametrizedPlaneSection
      (A.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)
      (fun j => (μ j).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : PlaneTransverse
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)) :
    ‖projectiveSectionTrace A ψ G u‖ ≤ (2 * (n : ℝ) - 1) * Real.sqrt p + 1 := by
  let i : ZMod p →+* AlgebraicClosure (ZMod p) := algebraMap _ _
  have hpull : (MvPolynomial.aeval μ G).IsHomogeneous (2 * n) :=
    hG.aeval μ c.homogeneous
  have hns : BinaryNonsingular ((MvPolynomial.aeval μ G).map i) := by
    rw [map_aeval_polynomial]
    apply transverse_pullback_nonsingular
      (matrixQuadraticPolynomial (A.map i)) (G.map i) (i ∘ u) (fun j => (μ j).map i)
      cgeom.quadric_identity cgeom.plane_identity cgeom.nonzero cgeom.partials
    simpa only [matrixQuadraticPolynomial_map] using htrans
  have hroots := binary_nonsingular_geometric_roots hpull (by omega) hns
  have horder2 : ψ ^ (2 * n) = 1 := by
    rw [Nat.mul_comm 2 n, pow_mul, horder, one_pow]
  rw [projectiveSectionTrace_eq_projectiveLine A u μ c ψ hG horder]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    projective_weil_bound p ψ hψ hpull hroots.1 (by omega) horder2 hroots.2

end QuaternaryQuadraticForms
