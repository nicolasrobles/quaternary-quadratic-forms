import QuaternaryQuadraticForms.SourceExceptionalPolynomials
import QuaternaryQuadraticForms.CongruenceBoxTheorem

/-!
# The complete source assertion of Lemma 3.10

The polynomial family is supplied only at the primes outside the source
modulus `N`. The unweighted set and the weighted sum use its literal
product indicator, the integral adjugate quadratic value and the actual
Euclidean norm. The final theorem allows a real degree bound, as in the
source, and chooses its constant before all coefficient and modulus data.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal solution set in the first assertion of Lemma 3.10. -/
def sourceCongruenceEuclideanSet (A : Matrix (Fin 4) (Fin 4) ℤ) (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (q h : ℕ) (hhN : h.Coprime N) (U : ℝ) : Set (Fin 4 → ℤ) :=
  {u | integerEuclideanNorm u ≤ U ∧
    (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) ∧
    sourceExceptionalIndicator N D h hhN u = 1}

/-- The finite internal representation counts exactly the source set. -/
theorem sourceCongruenceEuclideanSet_eq (A : Matrix (Fin 4) (Fin 4) ℤ) (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (q h : ℕ) (hhN : h.Coprime N) (U : ℝ) :
    sourceCongruenceEuclideanSet A N D q h hhN U =
      (congruenceEuclideanBall A (extendExceptionalPolynomials N D) q h U :
        Set (Fin 4 → ℤ)) := by
  ext u
  simp only [sourceCongruenceEuclideanSet, Set.mem_setOf_eq, Finset.mem_coe,
    mem_congruenceEuclideanBall, exceptionalIndicator_extend N D h hhN]

/-- The finite internal weighted sum is the source's actual product-indicator sum. -/
theorem sourceWeightedCongruenceEuclideanSum_eq
    (A : Matrix (Fin 4) (Fin 4) ℤ) (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (q h : ℕ) (hhN : h.Coprime N) (U : ℝ) :
    (∑ u ∈ divisibleEuclideanBall A q U,
      sourceExceptionalIndicator N D h hhN u / integerEuclideanNorm u) =
      weightedCongruenceEuclideanSum A (extendExceptionalPolynomials N D) q h U := by
  simp only [weightedCongruenceEuclideanSum, exceptionalIndicator_extend N D h hhN]

/-- Both clauses of Lemma 3.10 for a natural degree bound, retaining
the original good-prime polynomial domain and the literal indicator. -/
theorem source_congruence_box_natDegree (E : ℕ) (hE : 1 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), 1 ≤ N → primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), D p hp hpN ≠ 0) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), (D p hp hpN).totalDegree ≤ E) →
      ∀ (q h : ℕ), 1 ≤ q → 1 ≤ h → Squarefree q → Squarefree h →
        q.Coprime h → ∀ (hcopN : (q * h).Coprime N),
      ∀ (U : ℝ), 1 ≤ U →
        (sourceCongruenceEuclideanSet A N D q h
          (hcopN.of_dvd_left (dvd_mul_left h q)) U).Finite ∧
        ((sourceCongruenceEuclideanSet A N D q h
          (hcopN.of_dvd_left (dvd_mul_left h q)) U).ncard : ℝ) ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) ∧
        (∑ u ∈ divisibleEuclideanBall A q U,
          sourceExceptionalIndicator N D h (hcopN.of_dvd_left (dvd_mul_left h q)) u /
            integerEuclideanNorm u) ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 3 / ((q * h : ℕ) : ℝ) + U ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := congruenceBox_bounds E hE ε hε
  refine ⟨K, hK, ?_⟩
  intro A hA hdet N _hN hrad D hD hdeg q h hq hh hsq hsh hcop hcopN U hU
  obtain ⟨hcount, hweighted⟩ := hbound A hA hdet N hrad (extendExceptionalPolynomials N D)
    (extendExceptionalPolynomials_ne_zero N D hD)
    (extendExceptionalPolynomials_totalDegree_le N E D hdeg)
    q h hq hh hsq hsh hcop hcopN U hU
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceCongruenceEuclideanSet_eq]
    exact Finset.finite_toSet _
  · rw [sourceCongruenceEuclideanSet_eq, Set.ncard_coe_finset]
    exact hcount
  · rw [sourceWeightedCongruenceEuclideanSum_eq]
    exact hweighted

/-- Complete Lemma 3.10 with the source's real degree bound. The implied
constant is fixed before the matrix, source modulus, local polynomials,
coprime squarefree moduli, and radius. Both the literal count and the
literal inverse-Euclidean-norm weighted sum are bounded. -/
theorem source_congruence_box (E : ℝ) (hE : 1 ≤ E) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), 1 ≤ N → primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), D p hp hpN ≠ 0) →
        (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ((D p hp hpN).totalDegree : ℝ) ≤ E) →
      ∀ (q h : ℕ), 1 ≤ q → 1 ≤ h → Squarefree q → Squarefree h →
        q.Coprime h → ∀ (hcopN : (q * h).Coprime N),
      ∀ (U : ℝ), 1 ≤ U →
        (sourceCongruenceEuclideanSet A N D q h
          (hcopN.of_dvd_left (dvd_mul_left h q)) U).Finite ∧
        ((sourceCongruenceEuclideanSet A N D q h
          (hcopN.of_dvd_left (dvd_mul_left h q)) U).ncard : ℝ) ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) ∧
        (∑ u ∈ divisibleEuclideanBall A q U,
          sourceExceptionalIndicator N D h (hcopN.of_dvd_left (dvd_mul_left h q)) u /
            integerEuclideanNorm u) ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 3 / ((q * h : ℕ) : ℝ) + U ^ 2) := by
  have hceil : 1 ≤ Nat.ceil E := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hE)
  obtain ⟨K, hK, hbound⟩ := source_congruence_box_natDegree (Nat.ceil E) hceil ε hε
  refine ⟨K, hK, ?_⟩
  intro A hA hdet N hN hrad D hD hdeg
  have hnat : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N),
      (D p hp hpN).totalDegree ≤ Nat.ceil E := by
    intro p hp hpN
    exact_mod_cast (hdeg p hp hpN).trans (Nat.le_ceil E)
  exact hbound A hA hdet N hN hrad D hD hnat

end QuaternaryQuadraticForms
