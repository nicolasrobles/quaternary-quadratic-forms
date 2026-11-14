import QuaternaryQuadraticForms.CompleteSumAlgebra
import QuaternaryQuadraticForms.CompositeWeights
import QuaternaryQuadraticForms.MixedPhase

/-!
# The literal complete sums of Section 3

The mixed sum uses a unit modulo `c` and a vector modulo `q*c`. Its
quadratic-congruence condition makes its additive phase independent of
the unit's integer lift. Canonical lifts are used only to define the sum.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Precisely the local scalar invariance used by Lemma 3.1. -/
def PrimeWeightsInvariant (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) : Prop :=
  ∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
    ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y

/-- The summand of the manuscript's mixed complete sum, on integer representatives. -/
def mixedIntegerSummand (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (a : ℤ) (x : Fin 4 → ℤ) : ℂ :=
  if (q : ℤ) ∣ integralQuadraticValue A x then
    compositeWeight ξ q x * ZMod.stdAddChar
      ((a * integralQuadraticValue A x + dotProduct u x : ℤ) : ZMod (q * c))
  else 0

/-- The literal mixed sum `𝒮_{q,c}(u)` of the manuscript. -/
def mixedCompleteSum (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ a : (ZMod c)ˣ, ∑ x : Fin 4 → ZMod (q * c),
    mixedIntegerSummand ξ q c A u (((a : ZMod c).val : ℕ) : ℤ)
      (residueLift (q * c) x)

/-- The actual unweighted complete sum `S_c(u)`. -/
def unweightedCompleteSum (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ a : (ZMod c)ˣ, ∑ x : Fin 4 → ZMod c,
    ZMod.stdAddChar
      (((((a : ZMod c).val : ℕ) : ℤ) * integralQuadraticValue A (residueLift c x) +
        dotProduct u (residueLift c x) : ℤ) : ZMod c)

/-- The actual constrained Fourier sum `C_q(u)` with the source prime-product weight. -/
def constrainedFourierSum (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ x : Fin 4 → ZMod q,
    if (q : ℤ) ∣ integralQuadraticValue A (residueLift q x) then
      compositeWeight ξ q (residueLift q x) *
        ZMod.stdAddChar ((dotProduct u (residueLift q x) : ℤ) : ZMod q)
    else 0

/-- Changing the lift of the unit parameter modulo `c` preserves the full summand. -/
theorem mixedIntegerSummand_a_congr
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u x : Fin 4 → ℤ)
    (a b : ℤ) (hab : (a : ZMod c) = (b : ZMod c)) :
    mixedIntegerSummand ξ q c A u a x = mixedIntegerSummand ξ q c A u b x := by
  unfold mixedIntegerSummand
  split_ifs with hx
  · congr 1
    exact mixedPhase_lift_independent q c A x u a b hx hab
  · rfl

/-- Changing integer representatives of the vector modulo `q*c` preserves the summand. -/
theorem mixedIntegerSummand_x_congr
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (a : ℤ) (x y : Fin 4 → ℤ)
    (hxy : ∀ i, (x i : ZMod (q * c)) = (y i : ZMod (q * c))) :
    mixedIntegerSummand ξ q c A u a x = mixedIntegerSummand ξ q c A u a y := by
  have hqxy (i : Fin 4) : (x i : ZMod q) = (y i : ZMod q) := by
    have h := congrArg (ZMod.castHom (dvd_mul_right q c) (ZMod q)) (hxy i)
    simpa only [map_intCast] using h
  have hdiv := integralQuadraticValue_dvd_congr q A x y hqxy
  unfold mixedIntegerSummand
  by_cases hy : (q : ℤ) ∣ integralQuadraticValue A y
  · have hx := hdiv.mpr hy
    simp only [if_pos hx, if_pos hy]
    rw [compositeWeight_congr_mod ξ q (q * c) (dvd_mul_right q c) x y hxy]
    congr 2
    push_cast
    rw [integralQuadraticValue_congr_mod (q * c) A x y hxy,
      dotProduct_congr_mod (q * c) u x y hxy]
  · have hx : ¬(q : ℤ) ∣ integralQuadraticValue A x := fun hx => hy (hdiv.mp hx)
    simp only [if_neg hx, if_neg hy]

/-- All choices of integer representatives in the mixed sum are immaterial. -/
theorem mixedIntegerSummand_congr
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (a b : ℤ) (x y : Fin 4 → ℤ)
    (hab : (a : ZMod c) = (b : ZMod c))
    (hxy : ∀ i, (x i : ZMod (q * c)) = (y i : ZMod (q * c))) :
    mixedIntegerSummand ξ q c A u a x = mixedIntegerSummand ξ q c A u b y :=
  (mixedIntegerSummand_a_congr ξ q c A u x a b hab).trans
    (mixedIntegerSummand_x_congr ξ q c A u b x y hxy)

end QuaternaryQuadraticForms
