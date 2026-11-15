import QuaternaryQuadraticForms.DeltaSymbolDefinitions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Actual analytic objects for the delta-integral estimates

The real variables carry the Euclidean norm and canonical Lebesgue measure.
Weights may be complex-valued, as in Heath--Brown's definition. The kernel,
one-dimensional bump, and its mass are the fixed definitions from Lemma 2.1.
No analytic estimate or source premise is included in this module.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ContDiff
open MeasureTheory

/-- The actual Euclidean space of four real variables. -/
abbrev RealVector4 := EuclideanSpace ℝ (Fin 4)

/-- The three coordinates on a regular hypersurface graph. -/
abbrev RealVector3 := EuclideanSpace ℝ (Fin 3)

/-- The literal real quadratic value; integral source matrices are cast entrywise. -/
def realQuadraticValue (A : Matrix (Fin 4) (Fin 4) ℝ) (x : RealVector4) : ℝ :=
  dotProduct (WithLp.ofLp x) (A.mulVec (WithLp.ofLp x))

/-- The explicit gradient vector of a symmetric quadratic form. Its agreement
with the actual derivative is proved separately. -/
def realQuadraticGradient (A : Matrix (Fin 4) (Fin 4) ℝ)
    (x : RealVector4) : RealVector4 :=
  (2 : ℝ) • A.toEuclideanLin x

/-- A smooth weight with compact support in the source sense. -/
def IsSmoothWeight (W : RealVector4 → ℂ) : Prop :=
  ContDiff ℝ ∞ W ∧ HasCompactSupport W

/-- A literal ordered coordinate partial derivative, using standard unit vectors. -/
def weightCoordinateDerivative (k : ℕ) (I : Fin k → Fin 4)
    (W : RealVector4 → ℂ) (x : RealVector4) : ℂ :=
  iteratedFDeriv ℝ k W x (fun j => EuclideanSpace.single (I j) (1 : ℝ))

/-- The manuscript's common bounds on every coordinate partial derivative.
The bound is selected before the weight, the point, and the coordinate indices. -/
def UniformCoordinateDerivatives (𝒲 : Set (RealVector4 → ℂ)) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ W ∈ 𝒲, ∀ x : RealVector4,
    ∀ I : Fin k → Fin 4, ‖weightCoordinateDerivative k I W x‖ ≤ C

/-- The equivalent operator-norm formulation used for internal calculus bounds. -/
def UniformWeightDerivatives (𝒲 : Set (RealVector4 → ℂ)) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ W ∈ 𝒲, ∀ x : RealVector4,
    ‖iteratedFDeriv ℝ k W x‖ ≤ C

/-- The literal four-dimensional smoothing bump in equation (2.3). -/
def heathBrownTheta (x : RealVector4) : ℝ :=
  heathBrownBumpMass⁻¹ ^ 4 * ∏ i : Fin 4, heathBrownBaseBump (x i)

/-- The actual localized weight, with no scale factor absorbed into its definition. -/
def localizedWeight (W : RealVector4 → ℂ) (δ : ℝ) (y : RealVector4) :
    RealVector4 → ℂ :=
  fun x => W x * (heathBrownTheta (δ⁻¹ • (x - y)) : ℂ)

/-- The actual oscillatory delta integral, with the frequency held fixed when
differentiating in `r`. -/
def deltaIntegral (F : RealVector4 → ℝ) (w : RealVector4 → ℂ)
    (r : ℝ) (v : RealVector4) : ℂ :=
  ∫ x : RealVector4, w x * (heathBrownDeltaKernel (r, F x) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((-inner ℝ v x / r : ℝ) : ℂ))

/-- The coordinate insertion used for an actual hypersurface graph. -/
def graphPoint (t : ℝ) (y : RealVector3) : RealVector4 :=
  WithLp.toLp 2 (Fin.cons t (WithLp.ofLp y))

end QuaternaryQuadraticForms
