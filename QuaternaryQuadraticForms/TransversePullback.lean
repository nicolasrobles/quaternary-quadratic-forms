import QuaternaryQuadraticForms.BinaryNonsingular
import QuaternaryQuadraticForms.PolynomialChainRule
import QuaternaryQuadraticForms.QuadraticPlane
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Transverse pullbacks to a parametrized conic

The polynomial chain rule places the two tangent vectors in the common
annihilator of three gradients. In four-dimensional space, the two tangent
vectors and the three gradients cannot both be linearly independent.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open Module

/-- The gradient formed from the literal formal partial derivatives. -/
def polynomialGradient {K σ : Type*} [CommSemiring K]
    (H : MvPolynomial σ K) (x : σ → K) : σ → K :=
  fun i => MvPolynomial.eval x (MvPolynomial.pderiv i H)

/-- Pointwise evaluation of a vector of coordinate polynomials. -/
def polynomialVectorEval {K σ τ : Type*} [CommSemiring K]
    (μ : σ → MvPolynomial τ K) (x : τ → K) : σ → K :=
  fun i => MvPolynomial.eval x (μ i)

/-- Evaluation of one formal derivative of a vector of coordinate polynomials. -/
def polynomialVectorDerivative {K σ τ : Type*} [CommSemiring K]
    (μ : σ → MvPolynomial τ K) (i : τ) (x : τ → K) : σ → K :=
  fun j => MvPolynomial.eval x (MvPolynomial.pderiv i (μ j))

/-- Three independent covectors in four-space cannot annihilate two
independent vectors. The covectors here are identified using the actual dot product. -/
theorem independent_three_two_dot_impossible {K : Type*} [Field K]
    (v : Fin 3 → Fin 4 → K) (w : Fin 2 → Fin 4 → K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hpair : ∀ i j, dotProduct (v i) (w j) = 0) : False := by
  let e := dotProductEquiv K (Fin 4)
  let Φ : Submodule K (Module.Dual K (Fin 4 → K)) :=
    Submodule.span K (Set.range (e ∘ v))
  have hv' : LinearIndependent K (e ∘ v) :=
    hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hdim : Module.finrank K Φ = 3 := by
    simpa only [Φ, Fintype.card_fin] using finrank_span_eq_card hv'
  have hwm (j : Fin 2) : w j ∈ Φ.dualCoannihilator := by
    change w j ∈ ((Submodule.span K (Set.range (e ∘ v))).dualCoannihilator :
      Set (Fin 4 → K))
    rw [Submodule.coe_dualCoannihilator_span]
    rintro _ ⟨i, rfl⟩
    exact hpair i j
  let w' : Fin 2 → Φ.dualCoannihilator := fun j => ⟨w j, hwm j⟩
  have hw' : LinearIndependent K w' :=
    LinearIndependent.of_comp Φ.dualCoannihilator.subtype hw
  have hsmall := hw'.fintype_card_le_finrank
  have htotal := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
  rw [hdim, Module.finrank_fin_fun] at htotal
  simp only [Fintype.card_fin] at hsmall
  omega

/-- Each partial derivative of the plane polynomial is its corresponding coefficient. -/
theorem pderiv_planePolynomial {K : Type*} [Field K] (u : Fin 4 → K) (i : Fin 4) :
    MvPolynomial.pderiv i (planePolynomial u) = MvPolynomial.C (u i) := by
  classical
  simp [planePolynomial, Pi.single_apply]

/-- The gradient of the actual plane polynomial is its normal vector. -/
theorem polynomialGradient_plane {K : Type*} [Field K] (u x : Fin 4 → K) :
    polynomialGradient (planePolynomial u) x = u := by
  funext i
  simp only [polynomialGradient, pderiv_planePolynomial, MvPolynomial.eval_C]

/-- The evaluated polynomial chain rule as a dot product of actual vectors. -/
theorem eval_pderiv_pullback {K σ τ : Type*} [CommSemiring K] [Fintype σ]
    (H : MvPolynomial σ K) (μ : σ → MvPolynomial τ K) (i : τ) (x : τ → K) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.aeval μ H)) =
      dotProduct (polynomialGradient H (polynomialVectorEval μ x))
        (polynomialVectorDerivative μ i x) :=
  eval_pderiv_aeval_chain_rule H μ i x

/-- The rank-three transversality condition at every nonzero common geometric zero. -/
def PlaneTransverse {K : Type*} [Field K]
    (F G : MvPolynomial (Fin 4) K) (u : Fin 4 → K) : Prop :=
  ∀ x : Fin 4 → K, x ≠ 0 → MvPolynomial.eval x F = 0 →
    MvPolynomial.eval x G = 0 → dotProduct u x = 0 →
      LinearIndependent K ![polynomialGradient F x, polynomialGradient G x, u]

/-- Transversality and the independent derivatives of a genuine conic
parametrization imply that its polynomial pullback has no projective singular zero. -/
theorem transverse_pullback_nonsingular {K : Type*} [Field K]
    (F G : MvPolynomial (Fin 4) K) (u : Fin 4 → K)
    (μ : Fin 4 → MvPolynomial (Fin 2) K)
    (hF : MvPolynomial.aeval μ F = 0)
    (hplane : MvPolynomial.aeval μ (planePolynomial u) = 0)
    (hnonzero : ∀ x : Fin 2 → K, x ≠ 0 → polynomialVectorEval μ x ≠ 0)
    (hderiv : ∀ x : Fin 2 → K, x ≠ 0 →
      LinearIndependent K (fun i : Fin 2 => polynomialVectorDerivative μ i x))
    (htrans : PlaneTransverse F G u) :
    BinaryNonsingular (MvPolynomial.aeval μ G) := by
  intro x hx hGzero hsingular
  let y := polynomialVectorEval μ x
  have hyF : MvPolynomial.eval y F = 0 := by
    change MvPolynomial.eval (fun j => MvPolynomial.eval x (μ j)) F = 0
    rw [← eval_aeval_polynomial F μ x, hF]
    simp
  have hyG : MvPolynomial.eval y G = 0 := by
    change MvPolynomial.eval (fun j => MvPolynomial.eval x (μ j)) G = 0
    rw [← eval_aeval_polynomial G μ x]
    exact hGzero
  have hyplane : dotProduct u y = 0 := by
    rw [← eval_planePolynomial]
    change MvPolynomial.eval (fun j => MvPolynomial.eval x (μ j)) (planePolynomial u) = 0
    rw [← eval_aeval_polynomial (planePolynomial u) μ x, hplane]
    simp
  have hFder (i : Fin 2) :
      dotProduct (polynomialGradient F y) (polynomialVectorDerivative μ i x) = 0 := by
    rw [← eval_pderiv_pullback F μ i x, hF]
    simp
  have hGder (i : Fin 2) :
      dotProduct (polynomialGradient G y) (polynomialVectorDerivative μ i x) = 0 := by
    rw [← eval_pderiv_pullback G μ i x]
    exact hsingular i
  have hplaneder (i : Fin 2) :
      dotProduct u (polynomialVectorDerivative μ i x) = 0 := by
    rw [← polynomialGradient_plane u y, ← eval_pderiv_pullback (planePolynomial u) μ i x,
      hplane]
    simp
  apply independent_three_two_dot_impossible
    ![polynomialGradient F y, polynomialGradient G y, u]
    (fun i : Fin 2 => polynomialVectorDerivative μ i x)
    (htrans y (hnonzero x hx) hyF hyG hyplane) (hderiv x hx)
  intro i j
  fin_cases i
  · exact hFder j
  · exact hGder j
  · exact hplaneder j

end QuaternaryQuadraticForms
