import QuaternaryQuadraticForms.PoissonSummation
import QuaternaryQuadraticForms.PoissonCompleteSum
import QuaternaryQuadraticForms.PoissonScaling
import QuaternaryQuadraticForms.PoissonLatticeSupport

/-!
# The exact frequency and modulus terms in Lemma 5.1

The Fourier transform of the actual test function is converted to the
previously defined delta integral. Absolute convergence survives this
nonzero fixed scaling, and the kernel supplies a single finite modulus cutoff.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal mixed-complete-sum times delta-integral frequency term. -/
def poissonFrequencyTerm
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (u : Fin 4 → ℤ) : ℂ :=
  mixedCompleteSum ξ q (c : ℕ) A u *
    deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
      w ((c : ℝ) / (B / Real.sqrt (q : ℝ)))
      ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u)

/-- The literal c^(-4) weighted frequency series in equation (5.3). -/
def poissonModulusTerm
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) : ℂ :=
  ((c : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ, poissonFrequencyTerm ξ q A B w c u

set_option maxHeartbeats 800000 in
/-- For each modulus, the actual arithmetic lattice sum equals its scaled
frequency series, and the latter is absolutely convergent. -/
theorem poisson_test_function_complete_sum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w) (c : ℕ+) :
    ((∑ a : (ZMod (c : ℕ))ˣ, ∑' x : Fin 4 → ℤ,
      mixedIntegerSummand ξ q (c : ℕ) A 0
        ((a : ZMod (c : ℕ)).val : ℤ) x *
        poissonTestFunction A B (B / Real.sqrt (q : ℝ)) w c (integerRealVector x)) =
      ((B : ℂ) ^ 4 / (q : ℂ) ^ 4) * poissonModulusTerm ξ q A B w c) ∧
    Summable (fun u : Fin 4 → ℤ => ‖poissonFrequencyTerm ξ q A B w c u‖) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ : 0 < B / Real.sqrt (q : ℝ) :=
    div_pos hB (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hq))
  let g := poissonTestFunction A B (B / Real.sqrt (q : ℝ)) w c
  let f := fun u : Fin 4 → ℤ =>
    poissonFourierIntegral g (((q * (c : ℕ) : ℕ) : ℝ)⁻¹ • integerRealVector u)
  have hg : IsSmoothWeight g := poissonTestFunction_isSmoothWeight A B _ w c hB hQ hw
  obtain ⟨hf, hp⟩ := poisson_affine_integer_lattice g hg (q * (c : ℕ))
  obtain ⟨heq, hsum⟩ := poisson_mixed_complete_sum ξ q (c : ℕ) A g f
    (compactSupport_integerRealVector_finite g hg.2) hf hp
  have hscale (u : Fin 4 → ℤ) :
      mixedCompleteSum ξ q (c : ℕ) A u * f u =
        (B : ℂ) ^ 4 * poissonFrequencyTerm ξ q A B w c u := by
    dsimp only [f, g]
    rw [poissonFourierIntegral_testFunction A q B w c u hq hB]
    unfold poissonFrequencyTerm
    ac_rfl
  refine ⟨?_, ?_⟩
  · calc
      _ = (((q * (c : ℕ) : ℕ) : ℂ) ^ 4)⁻¹ *
          ((B : ℂ) ^ 4 * ∑' u : Fin 4 → ℤ, poissonFrequencyTerm ξ q A B w c u) := by
        rw [heq]
        congr 1
        exact (tsum_congr hscale).trans (tsum_mul_left)
      _ = _ := by
        simp only [poissonModulusTerm, Nat.cast_mul, mul_pow, mul_inv_rev, div_eq_mul_inv]
        ring
  · have hs : Summable (fun u : Fin 4 → ℤ =>
        ‖(B : ℂ) ^ 4‖ * ‖poissonFrequencyTerm ξ q A B w c u‖) := by
      exact hsum.congr (fun u => by rw [hscale u, norm_mul])
    have hn : ‖(B : ℂ) ^ 4‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      apply pow_ne_zero
      exact_mod_cast hB.ne'
    have hcancel (t : ℝ) : ‖(B : ℂ) ^ 4‖⁻¹ * (‖(B : ℂ) ^ 4‖ * t) = t := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    exact (hs.mul_left (‖(B : ℂ) ^ 4‖)⁻¹).congr
      (fun u => hcancel ‖poissonFrequencyTerm ξ q A B w c u‖)

/-- A single finite cutoff annihilates every actual frequency term. -/
theorem poissonFrequencyTerm_eventually_zero
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (hw : HasCompactSupport w) :
    ∃ K : ℕ, ∀ c : ℕ+, K < (c : ℕ) → ∀ u : Fin 4 → ℤ,
      poissonFrequencyTerm ξ q A B w c u = 0 := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨K, hK⟩ := poissonDeltaIntegral_eventually_zero A (B / Real.sqrt (q : ℝ)) w
    (div_pos hB (Real.sqrt_pos.mpr hq)) hw
  refine ⟨K, fun c hc u => ?_⟩
  simp only [poissonFrequencyTerm, hK c hc, mul_zero]

/-- The positive-modulus series has actual finite support. -/
theorem poissonModulusTerm_finite_support
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (hw : HasCompactSupport w) :
    (Function.support (poissonModulusTerm ξ q A B w)).Finite := by
  obtain ⟨K, hK⟩ := poissonFrequencyTerm_eventually_zero ξ q A B hB w hw
  let s : Finset ℕ+ := (Finset.Icc 1 K).subtype (fun c : ℕ => 0 < c)
  apply s.finite_toSet.subset
  intro c hc
  have hle : (c : ℕ) ≤ K := by
    by_contra hn
    have hz := hK c (Nat.lt_of_not_ge hn)
    exact hc (by simp [poissonModulusTerm, hz])
  change (⟨(c : ℕ), c.pos⟩ : {k : ℕ // 0 < k}) ∈
    (Finset.Icc 1 K).subtype (fun k : ℕ => 0 < k)
  rw [Finset.mem_subtype, Finset.mem_Icc]
  exact ⟨c.pos, hle⟩

end QuaternaryQuadraticForms
