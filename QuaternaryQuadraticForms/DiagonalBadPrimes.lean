import QuaternaryQuadraticForms.DiagonalReduction
import QuaternaryQuadraticForms.BadPrimeRadical

/-!
# The diagonal bad-prime lemma

The actual geometric criterion for the diagonal pair identifies its bad
primes with the prime divisors of the six-factor product `M`, away from
`N_F`. This gives finiteness directly and identifies the existing modulus
with `rad(|2 α M|)`, without an elimination premise or a surrogate modulus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual bad-prime set of the source diagonal pair is finite because
every additional bad prime divides the nonzero integer `M`. -/
theorem diagonal_badReductionPrimes_finite
    (a b : Fin 4 → ℤ)
    (hΔ : ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0) :
    (badReductionPrimes (Matrix.diagonal a)
      (matrixQuadraticPolynomial (Matrix.diagonal b))).Finite := by
  apply badReductionPrimes_finite_of_iff_dvd (Matrix.diagonal a)
    (matrixQuadraticPolynomial (Matrix.diagonal b)) (diagonalPairProduct a b)
    ((diagonalPairProduct_ne_zero_iff a b).mpr hΔ)
  intro p _ hpF
  exact diagonal_badReductionAt_iff p a b hpF

/-- The exact diagonal formula for the existing modulus, valid for every
proof of finiteness used to define it. Signs and shared prime divisors
are included in the literal absolute-value radical. -/
theorem diagonal_badPrimeModulus
    (a b : Fin 4 → ℤ) (hα : (∏ i, a i) ≠ 0)
    (hΔ : ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0)
    (hfinite : (badReductionPrimes (Matrix.diagonal a)
      (matrixQuadraticPolynomial (Matrix.diagonal b))).Finite) :
    polynomialBadPrimeModulus (Matrix.diagonal a)
      (matrixQuadraticPolynomial (Matrix.diagonal b)) hfinite =
        primeRadical (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs := by
  have hdet : (Matrix.diagonal a).det ≠ 0 := by
    simpa only [Matrix.det_diagonal] using hα
  calc
    polynomialBadPrimeModulus (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) hfinite =
      primeRadical (quadraticBadPrimeModulus (Matrix.diagonal a) *
        (diagonalPairProduct a b).natAbs) := by
      apply polynomialBadPrimeModulus_eq_primeRadical_of_bad_iff
        (Matrix.diagonal a) hdet (matrixQuadraticPolynomial (Matrix.diagonal b))
        (diagonalPairProduct a b) ((diagonalPairProduct_ne_zero_iff a b).mpr hΔ)
        _ hfinite
      intro p _ hpF
      exact diagonal_badReductionAt_iff p a b hpF
    _ = primeRadical (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs :=
      congrArg primeRadical (diagonal_bad_modulus_product a b)

/-- All clauses of Lemma 4.5 for the source diagonal forms: smoothness
in characteristic zero, the exact geometric bad-prime criterion, and the
literal radical formula. Finiteness is supplied by the preceding internal
deduction rather than assumed or imported from elimination. -/
theorem diagonal_bad_primes
    (a b : Fin 4 → ℤ) (hα : (∏ i, a i) ≠ 0)
    (hΔ : ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0) :
    SmoothCharacteristicZero (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus (Matrix.diagonal a) →
      (¬ GoodReductionAt p (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) ↔
          (p : ℤ) ∣ diagonalPairProduct a b)) ∧
    polynomialBadPrimeModulus (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b))
        (diagonal_badReductionPrimes_finite a b hΔ) =
      primeRadical (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs := by
  refine ⟨diagonal_smooth_characteristicZero a b hα hΔ, ?_,
    diagonal_badPrimeModulus a b hα hΔ _⟩
  intro p _ hpF
  exact diagonal_badReductionAt_iff p a b hpF

end QuaternaryQuadraticForms
