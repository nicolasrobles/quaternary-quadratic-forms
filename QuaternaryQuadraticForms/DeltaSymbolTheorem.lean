import QuaternaryQuadraticForms.Trusted.HeathBrown
import QuaternaryQuadraticForms.DeltaSymbolNormalization
import QuaternaryQuadraticForms.DeltaSymbolSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The complete source delta lemma

The fixed Heath--Brown construction supplies the common smooth kernel.
The source range, uniform positive normalization, rapid coefficient
estimate, normalized identity, and finite outer sum are proved deductions
from the separately registered construction-level literature input.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ContDiff

/-- The fixed source kernel is smooth on the open positive half-plane,
has the absolute size bound, and has the literal support in Lemma 2.1. -/
theorem heathBrownDeltaKernel_properties :
    ContDiffOn ℝ ∞ heathBrownDeltaKernel {z : ℝ × ℝ | 0 < z.1} ∧
    (∃ B : ℝ, 0 < B ∧ ∀ x y : ℝ, 0 < x →
      |heathBrownDeltaKernel (x, y)| ≤ B / x) ∧
    (∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x →
      heathBrownDeltaKernel (x, y) = 0) := by
  obtain ⟨_, _, _, _, hsmooth, hsize, hsupport, _, _⟩ :=
    Trusted.heathBrown_delta_data
  exact ⟨hsmooth, hsize, hsupport⟩

/-- The actual normalization denominator has one positive lower bound
for all real scales in the manuscript range. -/
theorem heathBrownSamplingSum_uniform_pos :
    ∃ d : ℝ, 0 < d ∧ ∀ Q : ℝ, 3 ≤ Q → d ≤ heathBrownSamplingSum Q := by
  obtain ⟨hc, hn, hp, hz, _, _, _, _, _⟩ := Trusted.heathBrown_delta_data
  have hz' (x : ℝ) (hx : 1 ≤ x) : heathBrownBump x = 0 :=
    hz x (fun h => (not_lt_of_ge hx) h.2)
  simpa only [heathBrownSamplingSum, bumpSamplingSum] using
    bumpSamplingSum_uniform_pos heathBrownBump hc hn hp hz'

/-- In particular the literal denominator in (3.3) is nonzero. -/
theorem heathBrownSamplingSum_pos (Q : ℝ) (hQ : 3 ≤ Q) :
    0 < heathBrownSamplingSum Q := by
  obtain ⟨d, hd, hb⟩ := heathBrownSamplingSum_uniform_pos
  exact hd.trans_le (hb Q hQ)

/-- The actual source coefficient is positive for every real `Q >= 3`. -/
theorem heathBrownNormalization_pos (Q : ℝ) (hQ : 3 ≤ Q) :
    0 < heathBrownNormalization Q :=
  div_pos (by linarith) (heathBrownSamplingSum_pos Q hQ)

/-- Every rapid-error constant is fixed before the scale. The bound
holds throughout `Q >= 3`, not merely eventually as `Q` tends to infinity. -/
theorem heathBrownNormalization_error_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      |heathBrownNormalization Q - 1| ≤ C / Q ^ j := by
  obtain ⟨hc, hn, hp, hz, _, _, _, _, hraw⟩ := Trusted.heathBrown_delta_data
  have hz' (x : ℝ) (hx : 1 ≤ x) : heathBrownBump x = 0 :=
    hz x (fun h => (not_lt_of_ge hx) h.2)
  have hraw' : ∀ m : ℕ, 2 ≤ m → ∃ A : ℝ, 0 < A ∧ ∀ Q : ℝ, 1 < Q →
      |bumpSamplingSum heathBrownBump Q - Q| ≤ A * Q / Q ^ m := by
    simpa only [bumpSamplingSum, heathBrownSamplingSum] using hraw
  simpa only [heathBrownNormalization, heathBrownSamplingSum, bumpSamplingSum] using
    bumpNormalization_error_bound heathBrownBump hc hn hp hz' hraw' j hj

/-- Real decay orders follow by rounding the order up before choosing
the constant. No new estimate or literature premise is needed. -/
theorem heathBrownNormalization_error_bound_real (j : ℝ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      |heathBrownNormalization Q - 1| ≤ C * Q ^ (-j) := by
  have hk : 1 ≤ Nat.ceil j := Nat.one_le_ceil_iff.mpr (by linarith)
  obtain ⟨C, hC, hbound⟩ := heathBrownNormalization_error_bound (Nat.ceil j) hk
  refine ⟨C, hC, ?_⟩
  intro Q hQ
  have hQone : 1 ≤ Q := by linarith
  calc
    |heathBrownNormalization Q - 1| ≤ C / Q ^ Nat.ceil j := hbound Q hQ
    _ = C * Q ^ (-(Nat.ceil j : ℝ)) := by
      rw [Real.rpow_neg (by linarith : 0 ≤ Q), Real.rpow_natCast, div_eq_mul_inv]
    _ ≤ C * Q ^ (-j) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQone (neg_le_neg (Nat.le_ceil j))) hC.le

/-- Divide the unnormalized source identity only after proving that
both actual denominators are positive. This is equation (2.1). -/
theorem heathBrown_delta_identity (Q : ℝ) (hQ : 3 ≤ Q) (n : ℤ) :
    (if n = 0 then 1 else 0 : ℂ) =
      ((heathBrownNormalization Q / Q ^ 2 : ℝ) : ℂ) *
        ∑' c : ℕ+, deltaSymbolTerm heathBrownDeltaKernel Q n c := by
  obtain ⟨_, _, _, _, _, _, _, hraw, _⟩ := Trusted.heathBrown_delta_data
  have hQpos : 0 < Q := by linarith
  have hSpos := heathBrownSamplingSum_pos Q hQ
  have hcoeff : (heathBrownNormalization Q / Q ^ 2) *
      (Q * heathBrownSamplingSum Q) = 1 := by
    unfold heathBrownNormalization
    field_simp
  have hcoeffC : ((heathBrownNormalization Q / Q ^ 2 : ℝ) : ℂ) *
      ((Q * heathBrownSamplingSum Q : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcoeff
  rw [hraw Q (by linarith) n, ← mul_assoc, hcoeffC, one_mul]

/-- A literal finite outer sum with the original unit-residue phases. -/
theorem heathBrown_delta_finite_identity (Q : ℝ) (hQ : 3 ≤ Q) (n : ℤ) :
    (if n = 0 then 1 else 0 : ℂ) =
      ((heathBrownNormalization Q / Q ^ 2 : ℝ) : ℂ) *
        ∑ c ∈ deltaSymbolModuli Q n, ∑ a : (ZMod (c : ℕ))ˣ,
          ZMod.stdAddChar ((a : ZMod (c : ℕ)) * (n : ZMod (c : ℕ))) *
            (heathBrownDeltaKernel ((c : ℝ) / Q, (n : ℝ) / Q ^ 2) : ℂ) := by
  rw [heathBrown_delta_identity Q hQ n,
    deltaSymbolTerm_tsum_eq_unit_sum heathBrownDeltaKernel
      heathBrownDeltaKernel_properties.2.2 Q (by linarith) n]

/-- Complete Lemma 2.1 with one common kernel and one normalization
function, all quantitative clauses, and the finite-support consequence.
The smooth order is `∞`; no analyticity is assumed. -/
theorem source_delta_symbol :
    ∃ (h : ℝ × ℝ → ℝ) (c : ℝ → ℝ),
      ContDiffOn ℝ ∞ h {z : ℝ × ℝ | 0 < z.1} ∧
      (∀ Q : ℝ, 3 ≤ Q → 0 < c Q) ∧
      (∀ Q : ℝ, 3 ≤ Q → ∀ n : ℤ,
        (if n = 0 then 1 else 0 : ℂ) =
          ((c Q / Q ^ 2 : ℝ) : ℂ) * ∑' q : ℕ+, deltaSymbolTerm h Q n q) ∧
      (∀ j : ℝ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
        |c Q - 1| ≤ C * Q ^ (-j)) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ x y : ℝ, 0 < x → |h (x, y)| ≤ B / x) ∧
      (∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0) ∧
      (∀ Q : ℝ, 3 ≤ Q → ∀ n : ℤ,
        (Function.support (deltaSymbolTerm h Q n)).Finite) := by
  obtain ⟨hsmooth, hsize, hsupport⟩ := heathBrownDeltaKernel_properties
  refine ⟨heathBrownDeltaKernel, heathBrownNormalization, hsmooth,
    heathBrownNormalization_pos, heathBrown_delta_identity,
    heathBrownNormalization_error_bound_real, hsize, hsupport, ?_⟩
  intro Q hQ n
  exact deltaSymbolTerm_finite_support heathBrownDeltaKernel hsupport Q (by linarith) n

end QuaternaryQuadraticForms
