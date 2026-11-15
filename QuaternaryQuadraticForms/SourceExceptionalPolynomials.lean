import QuaternaryQuadraticForms.CongruenceBoxDefinitions

/-!
# Exceptional polynomials supplied only at good primes

Section 3 supplies `D_p` only for prime `p` not dividing `N`.  Extending
by zero at other indices imposes no additional hypothesis.  The indicator
for a modulus coprime to `N` is exactly the product of the original
supplied local zero indicators.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The total family used by the internal congruence-box theorem. -/
def extendExceptionalPolynomials (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (p : ℕ) : MvPolynomial (Fin 4) (ZMod p) :=
  if hp : p.Prime then if hN : ¬p ∣ N then D p hp hN else 0 else 0

/-- At each allowed prime the extended polynomial is the supplied one. -/
theorem extendExceptionalPolynomials_apply (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (p : ℕ) (hp : p.Prime) (hN : ¬p ∣ N) :
    extendExceptionalPolynomials N D p = D p hp hN := by
  simp only [extendExceptionalPolynomials, dif_pos hp, dif_pos hN]

/-- The source nonvanishing hypothesis is preserved at every good prime. -/
theorem extendExceptionalPolynomials_ne_zero (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (hD : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), D p hp hN ≠ 0)
    (p : ℕ) (hp : p.Prime) (hN : ¬p ∣ N) :
    extendExceptionalPolynomials N D p ≠ 0 := by
  rw [extendExceptionalPolynomials_apply N D p hp hN]
  exact hD p hp hN

/-- The source degree bound is preserved at every good prime. -/
theorem extendExceptionalPolynomials_totalDegree_le (N E : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (hD : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), (D p hp hN).totalDegree ≤ E)
    (p : ℕ) (hp : p.Prime) (hN : ¬p ∣ N) :
    (extendExceptionalPolynomials N D p).totalDegree ≤ E := by
  rw [extendExceptionalPolynomials_apply N D p hp hN]
  exact hD p hp hN

/-- The literal source product `Delta_h(u)`, using only the supplied polynomials. -/
def sourceExceptionalIndicator (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (h : ℕ) (hhN : h.Coprime N) (u : Fin 4 → ℤ) : ℝ :=
  ∏ p : h.primeFactors,
    if MvPolynomial.eval (fun i => (u i : ZMod p.val))
      (D p.val (Nat.prime_of_mem_primeFactors p.property)
        ((Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
          (hhN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)))) = 0
    then 1 else 0

/-- No value at an excluded index enters the indicator of a coprime modulus. -/
theorem exceptionalIndicator_extend (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (h : ℕ) (hhN : h.Coprime N) (u : Fin 4 → ℤ) :
    exceptionalIndicator (extendExceptionalPolynomials N D) h u =
      sourceExceptionalIndicator N D h hhN u := by
  classical
  unfold exceptionalIndicator sourceExceptionalIndicator
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  rw [extendExceptionalPolynomials_apply N D p.val
    (Nat.prime_of_mem_primeFactors p.property)
    ((Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
      (hhN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)))]

/-- The empty-prime product gives the source convention `Delta_1(u)=1`. -/
theorem sourceExceptionalIndicator_one (N : ℕ)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (h : Nat.Coprime 1 N) (u : Fin 4 → ℤ) :
    sourceExceptionalIndicator N D 1 h u = 1 := by
  rw [← exceptionalIndicator_extend N D 1 h u]
  exact exceptionalIndicator_one (extendExceptionalPolynomials N D) u

end QuaternaryQuadraticForms
