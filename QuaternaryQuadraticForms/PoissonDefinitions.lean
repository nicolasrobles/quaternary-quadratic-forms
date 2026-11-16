import QuaternaryQuadraticForms.AnalyticDefinitions
import QuaternaryQuadraticForms.CompleteSums
import QuaternaryQuadraticForms.SourceCompositeWeights
import QuaternaryQuadraticForms.EuclideanIntegerBox

/-!
# The literal functions and lattice sums in Lemma 5.1

All real variables carry the Euclidean norm and canonical Lebesgue measure.
The kernel, source weights, complete sums, and oscillatory integral are the
previously fixed manuscript objects.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open MeasureTheory

/-- Coordinatewise inclusion of the actual integer lattice in Euclidean four-space. -/
def integerRealVector (x : Fin 4 → ℤ) : RealVector4 :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

/-- Fourier transform with the source normalization exp(-2*pi*i*inner(v,x)). -/
def poissonFourierIntegral (g : RealVector4 → ℂ) (v : RealVector4) : ℂ :=
  ∫ x : RealVector4, g x *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-inner ℝ v x : ℝ) : ℂ))

/-- The compactly supported smooth function g_c used before Poisson summation. -/
def poissonTestFunction (A : Matrix (Fin 4) (Fin 4) ℤ)
    (B Q : ℝ) (w : RealVector4 → ℂ) (c : ℕ+) (x : RealVector4) : ℂ :=
  w (B⁻¹ • x) *
    (heathBrownDeltaKernel ((c : ℝ) / Q,
      realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • x)) : ℂ)

/-- The literal weighted integer-zero sum, with the total-family representation. -/
def weightedQuadraticZeroSum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (w : RealVector4 → ℂ) : ℂ :=
  ∑' x : Fin 4 → ℤ, if integralQuadraticValue A x = 0 then
    w (B⁻¹ • integerRealVector x) * compositeWeight ξ q x else 0

/-- The source's T_q(B;w), retaining the original good-prime function family. -/
def sourceQuadraticZeroSum (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (w : RealVector4 → ℂ) : ℂ :=
  ∑' x : Fin 4 → ℤ, if integralQuadraticValue A x = 0 then
    w (B⁻¹ • integerRealVector x) * sourceCompositeWeight N ξ q hqN x else 0

end QuaternaryQuadraticForms
