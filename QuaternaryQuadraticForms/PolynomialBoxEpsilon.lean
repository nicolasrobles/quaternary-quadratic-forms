import QuaternaryQuadraticForms.PolynomialBoxTheorem
import QuaternaryQuadraticForms.PrimeFactorEpsilon

/-!
# The epsilon consequence of Lemma 2.4

The implied constant is chosen before the squarefree modulus, the
independently supplied prime polynomials, the intervals and their common
cardinality bound. The source endpoint retains the literal integer
solution set and proves its finiteness.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The epsilon form of the polynomial-box estimate for integer endpoints,
with one constant uniform in all modulus and coefficient data. -/
theorem polynomialBox_squarefree_card_le_rpow (n E : ℕ) (hn : 1 ≤ n) (hE : 1 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 1 ≤ m → Squarefree m →
      ∀ (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)),
        (∀ p ∈ m.primeFactors, P p ≠ 0) →
        (∀ p ∈ m.primeFactors, (P p).totalDegree ≤ E) →
        ∀ (a b : Fin n → ℤ) (Y : ℝ), 1 ≤ Y →
          (∀ i, ((Finset.Icc (a i) (b i)).card : ℝ) ≤ Y) →
          ((polynomialBoxSolutions m.primeFactors P a b).card : ℝ) ≤
            K * (m : ℝ) ^ ε * (Y ^ n / (m : ℝ) + Y ^ (n - 1)) := by
  have hC : (1 : ℝ) ≤ (polynomialBoxConstant n E : ℝ) := by
    exact_mod_cast polynomialBoxConstant_pos n E hn hE
  obtain ⟨K, hK, hbound⟩ := primeFactor_pow_le_rpow _ hC ε hε
  refine ⟨K, hK, ?_⟩
  intro m hm hsq P hP hdeg a b Y hY hI
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  exact (polynomialBox_squarefree_card_le n E m hn hE hm hsq P hP hdeg
    a b Y hY hI).trans (mul_le_mul_of_nonneg_right (hbound m hm hsq) (by positivity))

/-- The complete source epsilon consequence immediately after Lemma 2.4.
Its constant depends only on the dimension, degree bound and exponent. -/
theorem source_polynomial_box_epsilon (n E : ℕ) (hn : 1 ≤ n) (hE : 1 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 1 ≤ m → Squarefree m →
      ∀ (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) →
          MvPolynomial (Fin n) (ZMod p.val)),
        (∀ p, P p ≠ 0) → (∀ p, (P p).totalDegree ≤ E) →
        ∀ (I : Fin n → Set ℝ), (∀ i, (I i).OrdConnected) →
          ∀ (hfin : ∀ i, ((fun z : ℤ => (z : ℝ)) ⁻¹' I i).Finite)
            (Y : ℝ), 1 ≤ Y →
            (∀ i, (((hfin i).toFinset).card : ℝ) ≤ Y) →
            (sourcePolynomialBoxSet m P I).Finite ∧
              ((sourcePolynomialBoxSet m P I).ncard : ℝ) ≤
                K * (m : ℝ) ^ ε * (Y ^ n / (m : ℝ) + Y ^ (n - 1)) := by
  have hC : (1 : ℝ) ≤ (polynomialBoxConstant n E : ℝ) := by
    exact_mod_cast polynomialBoxConstant_pos n E hn hE
  obtain ⟨K, hK, hbound⟩ := primeFactor_pow_le_rpow _ hC ε hε
  refine ⟨K, hK, ?_⟩
  intro m hm hsq P hP hdeg I hI hfin Y hY hcard
  obtain ⟨hfinite, hcount⟩ := source_polynomial_box n E m hn hE hm hsq
    P hP hdeg I hI hfin Y hY hcard
  rw [← polynomialBoxConstant_eq_sum_Icc,
    ← polynomialBox_primeFactors_card_eq_omega] at hcount
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  exact ⟨hfinite, hcount.trans
    (mul_le_mul_of_nonneg_right (hbound m hm hsq) (by positivity))⟩

end QuaternaryQuadraticForms
