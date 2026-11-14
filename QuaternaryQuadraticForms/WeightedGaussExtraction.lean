import QuaternaryQuadraticForms.WeightedGaussStationaryPhase
import QuaternaryQuadraticForms.GoodPrime

/-!
# Extracting a scalar-invariant weight from the actual Gauss sum

On the stationary residues, multiplication by the adjugate gives
`adj(A) u = -(2 a det A) y` modulo `p`. At a good prime and a unit scalar,
this multiplier is nonzero, so the given scalar invariance makes the
weight constant on every surviving summand. The argument includes all
frequencies, including the zero vector.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem weighted_reduce_mulVec (p : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (y : Fin 4 → ℤ) :
    reduceFrequency p (A.mulVec y) =
      (reduceQuadraticMatrix p A).mulVec (reduceFrequency p y) := by
  ext i
  simp [reduceFrequency, reduceQuadraticMatrix, Matrix.mulVec, dotProduct]

private theorem weighted_reduce_adjugate_mulVec (p : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    reduceFrequency p (A.adjugate.mulVec u) =
      (reduceQuadraticMatrix p A).adjugate.mulVec (reduceFrequency p u) := by
  rw [weighted_reduce_mulVec]
  rw [reduceQuadraticMatrix, reduceQuadraticMatrix_adjugate]

/-- The actual stationary residue has the adjugate-frequency weight.
Only invariance under nonzero scalars is needed, also at zero frequency. -/
theorem stationary_weight_eq_adjugate (p : ℕ) [Fact p.Prime]
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ (r • y) = ξ y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (u y : Fin 4 → ℤ)
    (hy : reduceFrequency p ((2 * a) • A.mulVec y + u) = 0) :
    ξ (reduceFrequency p y) = ξ (reduceFrequency p (A.adjugate.mulVec u)) := by
  let B := reduceQuadraticMatrix p A
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr (goodPrime_ne_two p A hp))
  have ha' : (a : ZMod p) ≠ 0 :=
    fun hz => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hd : B.det ≠ 0 := goodPrime_reduced_det_ne_zero p A hp
  have hy' : (2 * (a : ZMod p)) • B.mulVec (reduceFrequency p y) +
      reduceFrequency p u = 0 := by
    have hred : reduceFrequency p ((2 * a) • A.mulVec y + u) =
        (2 * (a : ZMod p)) • B.mulVec (reduceFrequency p y) +
          reduceFrequency p u := by
      rw [← weighted_reduce_mulVec]
      ext i
      simp [reduceFrequency, Pi.smul_apply, smul_eq_mul]
    rwa [← hred]
  have hadj := congrArg (fun v => B.adjugate.mulVec v) hy'
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero, smul_smul] at hadj
  have hvec : reduceFrequency p (A.adjugate.mulVec u) =
      -(2 * (a : ZMod p) * B.det) • reduceFrequency p y := by
    rw [weighted_reduce_adjugate_mulVec]
    ext i
    have hi := congrFun hadj i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
    change B.adjugate.mulVec (reduceFrequency p u) i =
      -(2 * (a : ZMod p) * B.det) * reduceFrequency p y i
    linear_combination hi
  rw [hvec]
  exact (hξ _ (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 ha') hd)) _).symm

/-- At a good prime, the complete weighted inner sum is the literal
unweighted Gauss sum times the adjugate-frequency weight. -/
theorem weightedIntegralGaussSum_mul_extract (p m : ℕ)
    [Fact p.Prime] [NeZero m] (hpm : p ∣ m)
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ (r • y) = ξ y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (u : Fin 4 → ℤ) :
    weightedIntegralGaussSum p (m * p) ξ A a u =
      ξ (reduceFrequency p (A.adjugate.mulVec u)) *
        integralQuadraticGaussSum (m * p) A a u := by
  classical
  rw [← weightedIntegralGaussSum_one p (m * p) A a u,
    weightedIntegralGaussSum_stationary_expansion p m hpm ξ A hA a u,
    weightedIntegralGaussSum_stationary_expansion p m hpm (fun _ => 1) A hA a u,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : reduceFrequency p ((2 * a) • A.mulVec (residueLift m y) + u) = 0
  · rw [if_pos hy, stationary_weight_eq_adjugate p ξ hξ A hp a ha u (residueLift m y) hy]
    simp only [one_mul, mul_assoc]
  · simp only [if_neg hy, mul_zero]

/-- The source's weighted inner Gauss extraction for every exponent at least
two, with its literal good-prime and integral-unit hypotheses. -/
theorem weightedIntegralGaussSum_prime_power_extract (p j : ℕ) [Fact p.Prime]
    (hj : 2 ≤ j) (ξ : (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ (r • y) = ξ y)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (u : Fin 4 → ℤ) :
    weightedIntegralGaussSum p (p ^ j) ξ A a u =
      ξ (reduceFrequency p (A.adjugate.mulVec u)) *
        integralQuadraticGaussSum (p ^ j) A a u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hexp : 2 + k = (k + 1) + 1 := by omega
  simpa only [hexp, pow_succ] using weightedIntegralGaussSum_mul_extract p (p ^ (k + 1))
    (dvd_pow_self p (by omega)) ξ hξ A hA hp a ha u

end QuaternaryQuadraticForms
