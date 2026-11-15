import QuaternaryQuadraticForms.SourceGoodPrime
import QuaternaryQuadraticForms.IntegralGaussShift
import QuaternaryQuadraticForms.QuadricSmooth
import QuaternaryQuadraticForms.PolynomialBoxResidues
import Mathlib.Data.Nat.Squarefree

/-!
# The prime polynomials for Lemma 3.10

At a prime dividing `q` we impose the literal adjugate quadratic form;
at the remaining primes dividing `q*h` we impose the supplied polynomial
`D p`. Coprimality of `q` and `h` keeps the two conditions separate.
The exact congruence equivalence includes either modulus equal to one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual prime polynomial used for the modulus `q*h`. -/
def boxCongruencePolynomial (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)) (q p : ℕ) :
    MvPolynomial (Fin 4) (ZMod p) :=
  if p ∣ q then matrixQuadraticPolynomial (reduceQuadraticMatrix p A).adjugate else D p

/-- At every prime of the combined modulus the selected polynomial is
nonzero, using precisely the source's exclusion of primes dividing `N`. -/
theorem boxCongruencePolynomial_ne_zero
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (N : ℕ) (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (hD : ∀ p, p.Prime → ¬ p ∣ N → D p ≠ 0)
    (q h : ℕ) (hcopN : (q * h).Coprime N)
    (p : ℕ) (hp : p ∈ (q * h).primeFactors) :
    boxCongruencePolynomial A D q p ≠ 0 := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  letI : Fact p.Prime := ⟨hpp⟩
  have hpN : ¬ p ∣ N := hpp.coprime_iff_not_dvd.mp
    (hcopN.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  have hpF := source_not_dvd_quadraticBadPrimeModulus N p A hdet hrad hpN
  by_cases hpq : p ∣ q
  · rw [boxCongruencePolynomial, if_pos hpq]
    apply matrixQuadraticPolynomial_ne_zero
    · rw [Matrix.adjugate_transpose, reduceQuadraticMatrix_symmetric p A hA]
    · rw [Matrix.det_adjugate]
      exact pow_ne_zero _ (goodPrime_reduced_det_ne_zero p A hpF)
    · exact Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr (goodPrime_ne_two p A hpF))
  · rw [boxCongruencePolynomial, if_neg hpq]
    exact hD p hpp hpN

/-- The selected polynomials have degree at most the source bound
`max 2 E`, uniformly in the coefficients and the prime. -/
theorem boxCongruencePolynomial_totalDegree_le
    (A : Matrix (Fin 4) (Fin 4) ℤ) (N E : ℕ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (hD : ∀ p, p.Prime → ¬ p ∣ N → (D p).totalDegree ≤ E)
    (q h : ℕ) (hcopN : (q * h).Coprime N)
    (p : ℕ) (hp : p ∈ (q * h).primeFactors) :
    (boxCongruencePolynomial A D q p).totalDegree ≤ max 2 E := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpN : ¬ p ∣ N := hpp.coprime_iff_not_dvd.mp
    (hcopN.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  by_cases hpq : p ∣ q
  · rw [boxCongruencePolynomial, if_pos hpq]
    exact (matrixQuadraticPolynomial_totalDegree_le _).trans (le_max_left 2 E)
  · rw [boxCongruencePolynomial, if_neg hpq]
    exact (hD p hpp hpN).trans (le_max_right 2 E)

/-- Divisibility by a squarefree natural modulus is exactly vanishing
of the integer's reductions at all its prime divisors. -/
theorem squarefree_int_dvd_iff_primeFactors (q : ℕ) (hsq : Squarefree q) (z : ℤ) :
    (q : ℤ) ∣ z ↔ ∀ p ∈ q.primeFactors, (z : ZMod p) = 0 := by
  constructor
  · intro h p hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact (show (p : ℤ) ∣ (q : ℤ) by
      exact_mod_cast Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    have hm := primeProduct_modEq q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) z 0 (by simpa using h)
    rw [Nat.prod_primeFactors_of_squarefree hsq] at hm
    exact Int.modEq_zero_iff_dvd.mp hm

/-- The combined prime-polynomial conditions are precisely the source
divisibility condition and the vanishing of all supplied `D p` at `p | h`. -/
theorem boxCongruencePolynomial_eval_eq_zero_iff
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q h : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h) (hsq : Squarefree q)
    (hcop : q.Coprime h) (u : Fin 4 → ℤ) :
    (∀ p ∈ (q * h).primeFactors,
      MvPolynomial.eval (fun i => (u i : ZMod p)) (boxCongruencePolynomial A D q p) = 0) ↔
    (q : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) ∧
      ∀ p ∈ h.primeFactors, MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hh0 : h ≠ 0 := by omega
  have hqh0 : q * h ≠ 0 := mul_ne_zero hq0 hh0
  constructor
  · intro hall
    constructor
    · apply (squarefree_int_dvd_iff_primeFactors q hsq _).mpr
      intro p hp
      have hpall : p ∈ (q * h).primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero hqh0).mpr
          ⟨Nat.prime_of_mem_primeFactors hp,
            dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors hp) h⟩
      have he := hall p hpall
      rw [boxCongruencePolynomial, if_pos (Nat.dvd_of_mem_primeFactors hp),
        eval_matrixQuadraticPolynomial, ← adjugateQuadraticValue_intCast] at he
      exact he
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hph := Nat.dvd_of_mem_primeFactors hp
      have hpq : ¬ p ∣ q := hpp.coprime_iff_not_dvd.mp (hcop.symm.of_dvd_left hph)
      have hpall : p ∈ (q * h).primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero hqh0).mpr ⟨hpp, dvd_mul_of_dvd_right hph q⟩
      have he := hall p hpall
      simpa only [boxCongruencePolynomial, if_neg hpq] using he
  · rintro ⟨hdual, hD⟩ p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hpq : p ∣ q
    · rw [boxCongruencePolynomial, if_pos hpq, eval_matrixQuadraticPolynomial,
        ← adjugateQuadraticValue_intCast]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      exact (show (p : ℤ) ∣ (q : ℤ) by exact_mod_cast hpq).trans hdual
    · rw [boxCongruencePolynomial, if_neg hpq]
      have hph : p ∣ h := (hpp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp)).resolve_left hpq
      exact hD p ((Nat.mem_primeFactors_of_ne_zero hh0).mpr ⟨hpp, hph⟩)

end QuaternaryQuadraticForms
