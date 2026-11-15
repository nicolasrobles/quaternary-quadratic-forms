import QuaternaryQuadraticForms.EuclideanIntegerBox
import QuaternaryQuadraticForms.MatrixPolynomial

/-!
# The literal sets and indicator in Lemma 3.10

The indicator is the product of the actual prime polynomial zero indicators.
The finite sets retain the integral adjugate quadratic value and the Euclidean
norm. The weighted sum includes every nonzero vector satisfying the dual
divisibility condition, with its original indicator weight.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The product `Delta_h(u)` of the source's polynomial zero indicators. -/
def exceptionalIndicator (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (h : ℕ) (u : Fin 4 → ℤ) : ℝ := by
  classical
  exact ∏ p ∈ h.primeFactors,
    if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0

/-- The product is exactly the indicator of all its prime congruences. -/
theorem exceptionalIndicator_eq_ite
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (h : ℕ) (u : Fin 4 → ℤ) :
    exceptionalIndicator D h u =
      if ∀ p ∈ h.primeFactors,
        MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0 := by
  classical
  unfold exceptionalIndicator
  by_cases hz : ∀ p ∈ h.primeFactors,
      MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0
  · rw [if_pos hz]
    exact Finset.prod_eq_one (fun p hp => if_pos (hz p hp))
  · rw [if_neg hz]
    push_neg at hz
    obtain ⟨p, hp, hne⟩ := hz
    exact Finset.prod_eq_zero hp (if_neg hne)

/-- The indicator equals one precisely when every required congruence holds. -/
theorem exceptionalIndicator_eq_one_iff
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (h : ℕ) (u : Fin 4 → ℤ) :
    exceptionalIndicator D h u = 1 ↔
      ∀ p ∈ h.primeFactors,
        MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 := by
  classical
  rw [exceptionalIndicator_eq_ite]
  split_ifs <;> simp_all

/-- Every indicator that is not one is zero. -/
theorem exceptionalIndicator_eq_zero_of_ne_one
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (h : ℕ) (u : Fin 4 → ℤ)
    (hu : exceptionalIndicator D h u ≠ 1) : exceptionalIndicator D h u = 0 := by
  classical
  rw [exceptionalIndicator_eq_ite]
  exact if_neg (mt (exceptionalIndicator_eq_one_iff D h u).mpr hu)

/-- Modulus one has the empty product indicator one. -/
theorem exceptionalIndicator_one
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (u : Fin 4 → ℤ) :
    exceptionalIndicator D 1 u = 1 := by
  simp [exceptionalIndicator]

/-- The actual integer vectors counted in the first clause of Lemma 3.10. -/
def congruenceEuclideanBall (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (q h : ℕ) (U : ℝ) :
    Finset (Fin 4 → ℤ) := by
  classical
  exact (integerEuclideanBall U).filter fun u =>
    (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) ∧ exceptionalIndicator D h u = 1

/-- Membership is exactly the unweighted source condition. -/
theorem mem_congruenceEuclideanBall (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (q h : ℕ) (U : ℝ)
    (u : Fin 4 → ℤ) :
    u ∈ congruenceEuclideanBall A D q h U ↔
      integerEuclideanNorm u ≤ U ∧
        (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) ∧ exceptionalIndicator D h u = 1 := by
  classical
  simp only [congruenceEuclideanBall, Finset.mem_filter, mem_integerEuclideanBall]

/-- The finite summation range in the weighted source assertion. -/
def divisibleEuclideanBall (A : Matrix (Fin 4) (Fin 4) ℤ) (q : ℕ) (U : ℝ) :
    Finset (Fin 4 → ℤ) := by
  classical
  exact (integerEuclideanBall U).filter fun u =>
    u ≠ 0 ∧ (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u)

/-- Membership retains the positive Euclidean radius and literal divisibility. -/
theorem mem_divisibleEuclideanBall (A : Matrix (Fin 4) (Fin 4) ℤ)
    (q : ℕ) (U : ℝ) (u : Fin 4 → ℤ) :
    u ∈ divisibleEuclideanBall A q U ↔
      0 < integerEuclideanNorm u ∧ integerEuclideanNorm u ≤ U ∧
        (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) := by
  classical
  simp only [divisibleEuclideanBall, Finset.mem_filter, mem_integerEuclideanBall,
    integerEuclideanNorm_pos_iff]
  tauto

/-- The actual inverse-norm weighted sum with its source indicator. -/
def weightedCongruenceEuclideanSum (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (q h : ℕ) (U : ℝ) : ℝ :=
  ∑ u ∈ divisibleEuclideanBall A q U, exceptionalIndicator D h u / integerEuclideanNorm u

/-- The original weighted sum equals the reciprocal-radius sum over
the nonzero congruence solutions. -/
theorem weightedCongruenceEuclideanSum_eq (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (q h : ℕ) (U : ℝ) :
    weightedCongruenceEuclideanSum A D q h U =
      ∑ u ∈ (congruenceEuclideanBall A D q h U).filter (fun u => u ≠ 0),
        1 / integerEuclideanNorm u := by
  classical
  simp only [weightedCongruenceEuclideanSum, divisibleEuclideanBall,
    congruenceEuclideanBall, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hd : exceptionalIndicator D h u = 1
  · by_cases hq : (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) <;> simp [hd, hq]
  · simp [exceptionalIndicator_eq_zero_of_ne_one D h u hd]

end QuaternaryQuadraticForms
