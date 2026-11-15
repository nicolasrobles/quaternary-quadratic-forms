import QuaternaryQuadraticForms.DeltaSymbolDefinitions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.PNat.Interval
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Finite support of the actual delta-symbol sum

The support condition on a real kernel gives an explicit finite set of
positive moduli. All results in this file are proved for an arbitrary
kernel satisfying that condition; no literature premise is used.
The unit-residue and exponential formulas retain the literal source
phase, including the single residue class at modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The delta summand is the literal sum over invertible residue classes. -/
theorem deltaSymbolTerm_eq_unit_sum (h : ℝ × ℝ → ℝ) (Q : ℝ) (n : ℤ)
    (c : ℕ+) :
    deltaSymbolTerm h Q n c =
      ∑ a : (ZMod (c : ℕ))ˣ,
        ZMod.stdAddChar ((a : ZMod (c : ℕ)) * (n : ZMod (c : ℕ))) *
          (h ((c : ℝ) / Q, (n : ℝ) / Q ^ 2) : ℂ) := by
  simp only [deltaSymbolTerm, integralRamanujanSum, residueRamanujanSum,
    Finset.sum_mul]

/-- The same summand written with the source complex exponential and an
integer representative of each invertible residue class. -/
theorem deltaSymbolTerm_eq_exponential_sum (h : ℝ × ℝ → ℝ) (Q : ℝ)
    (n : ℤ) (c : ℕ+) :
    deltaSymbolTerm h Q n c =
      ∑ a : (ZMod (c : ℕ))ˣ,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((a : ZMod (c : ℕ)).val : ℂ) * (n : ℂ)) / (c : ℂ)) *
          (h ((c : ℝ) / Q, (n : ℝ) / Q ^ 2) : ℂ) := by
  rw [deltaSymbolTerm, integralRamanujanSum_eq_lift_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ZMod.stdAddChar_coe]
  simp only [Int.cast_mul, Int.cast_natCast]

/-- At modulus one the unit sum consists of its single trivial phase. -/
theorem deltaSymbolTerm_modulus_one (h : ℝ × ℝ → ℝ) (Q : ℝ) (n : ℤ) :
    deltaSymbolTerm h Q n 1 = (h (1 / Q, (n : ℝ) / Q ^ 2) : ℂ) := by
  simp [deltaSymbolTerm, integralRamanujanSum_modulus_one]

/-- A support cutoff before specializing the second kernel coordinate.
This form also applies to the later Poisson integrand. -/
theorem deltaSymbolKernel_eq_zero_of_modulus_bound (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (c : ℕ+) (y : ℝ)
    (hc : Q * max 1 (2 * |y|) < (c : ℝ)) :
    h ((c : ℝ) / Q, y) = 0 := by
  have hcpos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr c.pos
  apply hsupport _ _ (div_pos hcpos hQ)
  exact (lt_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hc)

/-- The literal modulus term vanishes above the real support bound. -/
theorem deltaSymbolTerm_eq_zero_of_modulus_bound (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) (c : ℕ+)
    (hc : Q * max 1 (2 * |(n : ℝ) / Q ^ 2|) < (c : ℝ)) :
    deltaSymbolTerm h Q n c = 0 := by
  rw [deltaSymbolTerm,
    deltaSymbolKernel_eq_zero_of_modulus_bound h hsupport Q hQ c _ hc]
  simp

/-- The scaled kernel support is exactly the usual displayed cutoff
`max Q (2 * |n| / Q)` for a positive real scale. -/
theorem deltaSymbol_modulus_bound_eq_max (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    Q * max 1 (2 * |(n : ℝ) / Q ^ 2|) = max Q (2 * |(n : ℝ)| / Q) := by
  have hsecond : Q * (2 * |(n : ℝ) / Q ^ 2|) = 2 * |(n : ℝ)| / Q := by
    rw [abs_div, abs_of_nonneg (sq_nonneg Q), ← mul_div_assoc,
      ← mul_div_assoc, pow_two, mul_div_mul_left _ _ hQ.ne']
  rw [mul_max_of_nonneg _ _ hQ.le, mul_one, hsecond]

/-- The largest possible positive integer modulus in the kernel support. -/
def deltaSymbolCutoff (Q : ℝ) (n : ℤ) : ℕ :=
  ⌊Q * max 1 (2 * |(n : ℝ) / Q ^ 2|)⌋₊

/-- Precisely the positive integer moduli at or below the floor cutoff. -/
def deltaSymbolModuli (Q : ℝ) (n : ℤ) : Finset ℕ+ :=
  (Finset.Icc 1 (deltaSymbolCutoff Q n)).subtype (fun c : ℕ => 0 < c)

/-- Membership in the finite cutoff set is the source integer inequality. -/
@[simp] theorem mem_deltaSymbolModuli (Q : ℝ) (n : ℤ) (c : ℕ+) :
    c ∈ deltaSymbolModuli Q n ↔ (c : ℕ) ≤ deltaSymbolCutoff Q n := by
  change (⟨(c : ℕ), c.pos⟩ : {k : ℕ // 0 < k}) ∈
      (Finset.Icc 1 (deltaSymbolCutoff Q n)).subtype (fun k : ℕ => 0 < k) ↔ _
  rw [Finset.mem_subtype, Finset.mem_Icc]
  exact and_iff_right c.pos

/-- Every term outside the displayed finite cutoff set is zero. -/
theorem deltaSymbolTerm_eq_zero_of_not_mem (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) (c : ℕ+)
    (hc : c ∉ deltaSymbolModuli Q n) :
    deltaSymbolTerm h Q n c = 0 := by
  apply deltaSymbolTerm_eq_zero_of_modulus_bound h hsupport Q hQ n c
  apply Nat.lt_of_floor_lt
  exact Nat.lt_of_not_ge ((mem_deltaSymbolModuli Q n c).not.mp hc)

/-- The modulus support is finite, for every real positive scaling parameter. -/
theorem deltaSymbolTerm_finite_support (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    (Function.support (deltaSymbolTerm h Q n)).Finite := by
  apply (deltaSymbolModuli Q n).finite_toSet.subset
  intro c hc
  by_contra hnmem
  exact hc (deltaSymbolTerm_eq_zero_of_not_mem h hsupport Q hQ n c hnmem)

/-- The source modulus series is summable because only finitely many terms
can be nonzero, rather than by an additional convergence assumption. -/
theorem deltaSymbolTerm_summable (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    Summable (deltaSymbolTerm h Q n) := by
  exact summable_of_ne_finset_zero
    (deltaSymbolTerm_eq_zero_of_not_mem h hsupport Q hQ n)

/-- Absolute summability also follows directly from the finite cutoff. -/
theorem deltaSymbolTerm_norm_summable (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    Summable (fun c : ℕ+ => ‖deltaSymbolTerm h Q n c‖) := by
  apply summable_of_ne_finset_zero (s := deltaSymbolModuli Q n)
  intro c hc
  rw [deltaSymbolTerm_eq_zero_of_not_mem h hsupport Q hQ n c hc, norm_zero]

/-- The displayed finite sum is the value of the actual positive-modulus
series. -/
theorem deltaSymbolTerm_hasSum (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    HasSum (deltaSymbolTerm h Q n)
      (∑ c ∈ deltaSymbolModuli Q n, deltaSymbolTerm h Q n c) := by
  exact hasSum_sum_of_ne_finset_zero
    (deltaSymbolTerm_eq_zero_of_not_mem h hsupport Q hQ n)

/-- An explicit finite-cutoff form of the outer sum in the delta identity. -/
theorem deltaSymbolTerm_tsum_eq_sum (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    (∑' c : ℕ+, deltaSymbolTerm h Q n c) =
      ∑ c ∈ deltaSymbolModuli Q n, deltaSymbolTerm h Q n c :=
  (deltaSymbolTerm_hasSum h hsupport Q hQ n).tsum_eq

/-- Reindexing the exact positive-modulus cutoff by `c = k + 1`. -/
theorem deltaSymbolModuli_sum_eq_sum_range (Q : ℝ) (n : ℤ) (f : ℕ+ → ℂ) :
    (∑ c ∈ deltaSymbolModuli Q n, f c) =
      ∑ k ∈ Finset.range (deltaSymbolCutoff Q n), f k.succPNat := by
  classical
  apply Finset.sum_bij (fun c _ => c.natPred)
  · intro c hc
    have hc' := (mem_deltaSymbolModuli Q n c).mp hc
    apply Finset.mem_range.mpr
    exact (Nat.sub_lt c.pos (by decide : 0 < 1)).trans_le hc'
  · intro c _ d _ hcd
    exact Equiv.pnatEquivNat.injective hcd
  · intro k hk
    refine ⟨k.succPNat, ?_, ?_⟩
    · apply (mem_deltaSymbolModuli Q n k.succPNat).mpr
      simpa only [Nat.succPNat_coe, Nat.succ_le_iff] using Finset.mem_range.mp hk
    · simp
  · intro c _
    simp

/-- A natural-range presentation of the same finite modulus series. -/
theorem deltaSymbolTerm_tsum_eq_sum_range (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    (∑' c : ℕ+, deltaSymbolTerm h Q n c) =
      ∑ k ∈ Finset.range (deltaSymbolCutoff Q n),
        deltaSymbolTerm h Q n k.succPNat := by
  rw [deltaSymbolTerm_tsum_eq_sum h hsupport Q hQ n,
    deltaSymbolModuli_sum_eq_sum_range]

/-- The finite version retains the literal inner unit-residue sum. -/
theorem deltaSymbolTerm_tsum_eq_unit_sum (h : ℝ × ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x → h (x, y) = 0)
    (Q : ℝ) (hQ : 0 < Q) (n : ℤ) :
    (∑' c : ℕ+, deltaSymbolTerm h Q n c) =
      ∑ c ∈ deltaSymbolModuli Q n, ∑ a : (ZMod (c : ℕ))ˣ,
        ZMod.stdAddChar ((a : ZMod (c : ℕ)) * (n : ZMod (c : ℕ))) *
          (h ((c : ℝ) / Q, (n : ℝ) / Q ^ 2) : ℂ) := by
  rw [deltaSymbolTerm_tsum_eq_sum h hsupport Q hQ n]
  apply Finset.sum_congr rfl
  intro c _
  exact deltaSymbolTerm_eq_unit_sum h Q n c

end QuaternaryQuadraticForms
