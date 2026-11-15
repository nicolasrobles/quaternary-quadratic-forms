import QuaternaryQuadraticForms.SurfaceIntegralDefinitions
import QuaternaryQuadraticForms.SignedCoordinateChanges
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Quantitative versions of the source analytic classes

These are definitions of the actual functions, derivatives, and integrals
in Heath--Brown, Sections 2 and 6--8. No analytic estimate is assumed here.
The bounds are explicit parameters, so a source constant cannot secretly
depend on an individual weight or amplitude. Smoothness uses order infinity.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped ContDiff Topology

/-- The last three actual Euclidean coordinates. -/
def realVectorTail (x : RealVector4) : RealVector3 :=
  WithLp.toLp 2 (fun i : Fin 3 => x i.succ)

/-- Quantitative source class C(S), with the Euclidean support bound implying
the source's coordinate-cube bound. -/
def HBWeightControl (B : ℝ) (D : ℕ → ℝ) (w : RealVector4 → ℂ) : Prop :=
  IsSmoothWeight w ∧
  (∀ x ∈ tsupport w, ‖x‖ ≤ B) ∧
  ∀ k x I, ‖weightCoordinateDerivative k I w x‖ ≤ D k

/-- The literal interval and positive derivative conditions defining C₀(S).
No globally consistent root is assumed in this predicate. -/
def HBC0Geometry (F : RealVector4 → ℝ) (a lam : ℝ)
    (w : RealVector4 → ℂ) : Prop :=
  (∀ x ∈ tsupport w, ∀ t : ℝ, |t - x 0| ≤ a →
    lam ≤ gradient F (graphPoint t (realVectorTail x)) 0) ∧
  ∀ x ∈ tsupport w, ∃! t : ℝ,
    |t - x 0| ≤ a ∧ F (graphPoint t (realVectorTail x)) = 0

/-- The source local class with all common bounds exposed. -/
def HBC0Control (F : RealVector4 → ℝ) (B : ℝ) (D : ℕ → ℝ)
    (a lam : ℝ) (w : RealVector4 → ℂ) : Prop :=
  HBWeightControl B D w ∧ HBC0Geometry F a lam w

/-- Projection of the actual closed support, the domain in HB Theorem 3. -/
def weightTailSupport (w : RealVector4 → ℂ) : Set RealVector3 :=
  realVectorTail '' tsupport w

/-- A consistent root selector must actually select each source interval's
root. Its construction for a quadratic form is an internal obligation. -/
def HBGraphSelector (F : RealVector4 → ℝ) (w : RealVector4 → ℂ)
    (a : ℝ) (φ : RealVector3 → ℝ) : Prop :=
  ∀ x ∈ tsupport w,
    |φ (realVectorTail x) - x 0| ≤ a ∧
      F (surfaceGraph φ (realVectorTail x)) = 0

/-- The literal graph-coordinate expression in HB Theorem 3. -/
def hbGraphIntegral (F : RealVector4 → ℝ) (w : RealVector4 → ℂ)
    (φ : RealVector3 → ℝ) : ℂ :=
  ∫ y in weightTailSupport w,
    w (surfaceGraph φ y) / (gradient F (surfaceGraph φ y) 0 : ℂ)

/-- The source envelope, with its correct value one at t=0. -/
def HBAmplitudeEnvelope (N : ℕ) (r t : ℝ) : ℝ :=
  (r / max r |t|) ^ N

/-- Quantitative H-class (HB (7.1)). Bounds are common over all amplitudes
to which an oscillatory estimate is applied. -/
def HBAmplitudeControl (K : ℕ → ℕ → ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0 < z.1} ∧
  (∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 < r →
    ‖f (r, t)‖ ≤ K 0 N * (r ^ N + HBAmplitudeEnvelope N r t)) ∧
  ∀ j N : ℕ, 1 ≤ j → 1 ≤ N → ∀ r t : ℝ, 0 < r →
    ‖iteratedDeriv j (fun z => f (r, z)) t‖ ≤
      K j N * (r⁻¹ ^ j * HBAmplitudeEnvelope N r t)

/-- The actual auxiliary integral I(r;u) from HB Lemma 14. -/
def hbOscillatoryIntegral (F : RealVector4 → ℝ) (w : RealVector4 → ℂ)
    (f : ℝ × ℝ → ℂ) (r : ℝ) (u : RealVector4) : ℂ :=
  ∫ x : RealVector4, w x * f (r, F x) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-inner ℝ u x : ℝ) : ℂ))

/-- The actual matrix of second derivatives, not a substituted coefficient
matrix. The quadratic specialization must prove its equality with 2A. -/
def realHessian (F : RealVector4 → ℝ) (x : RealVector4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (fderiv ℝ (gradient F) x (EuclideanSpace.single j (1 : ℝ))) i

end QuaternaryQuadraticForms

