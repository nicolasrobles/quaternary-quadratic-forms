import QuaternaryQuadraticForms.GoodReduction
import Mathlib.Data.Nat.PrimeFin

/-!
# An exact radical formula from the geometric bad-prime criterion

Suppose that, away from the quadratic bad-prime modulus, failure of the
actual geometric good-reduction condition is equivalent to divisibility
of one fixed nonzero integer. The actual bad-prime set is then finite,
and its finite set is the prime divisors of that integer with the prime
divisors of the quadratic modulus removed. The existing product defining
`N_G` consequently equals the radical of the product of these two integers.

This is the arithmetic deduction in Lemma 4.5. The diagonal geometry will
supply the criterion with the manuscript's product of pairwise determinants.
No elimination theorem or replacement modulus is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- An exact divisibility criterion for geometric bad reduction implies
finiteness of the actual bad-prime set, directly from the nonzero integer. -/
theorem badReductionPrimes_finite_of_iff_dvd
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (z : ℤ) (hz : z ≠ 0)
    (hbad : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      (¬ GoodReductionAt p A G ↔ (p : ℤ) ∣ z)) :
    (badReductionPrimes A G).Finite := by
  apply badReductionPrimes_finite_of_common_divisor A G z hz
  intro p hp
  obtain ⟨hprime, haway, hnotgood⟩ := hp
  letI : Fact p.Prime := ⟨hprime⟩
  exact (hbad p haway).mp hnotgood

/-- The actual bad primes are precisely the prime factors of the criterion
integer which are absent from the quadratic bad-prime modulus. -/
theorem badReductionPrimes_toFinset_eq_primeFactors_sdiff
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0)
    (G : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hbad : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      (¬ GoodReductionAt p A G ↔ (p : ℤ) ∣ z))
    (hfinite : (badReductionPrimes A G).Finite) :
    hfinite.toFinset =
      z.natAbs.primeFactors \ (quadraticBadPrimeModulus A).primeFactors := by
  classical
  ext p
  rw [hfinite.mem_toFinset, Finset.mem_sdiff]
  constructor
  · rintro ⟨hprime, haway, hnotgood⟩
    letI : Fact p.Prime := ⟨hprime⟩
    have hdiv := (hbad p haway).mp hnotgood
    refine ⟨Nat.mem_primeFactors.mpr ⟨hprime, ?_, Int.natAbs_ne_zero.mpr hz⟩, ?_⟩
    · exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
    · intro hp
      exact haway (Nat.mem_primeFactors.mp hp).2.1
  · rintro ⟨hpz, hpA⟩
    obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hpz
    letI : Fact p.Prime := ⟨hprime⟩
    have haway : ¬ p ∣ quadraticBadPrimeModulus A := by
      intro hp
      apply hpA
      exact (Nat.mem_primeFactors_of_ne_zero
        (quadraticBadPrimeModulus_ne_zero A hdet)).mpr ⟨hprime, hp⟩
    refine ⟨hprime, haway, (hbad p haway).mpr ?_⟩
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdiv)

/-- The literal modulus `N_G` equals the radical of `N_F * |z|` when
geometric bad reduction away from `N_F` is exactly divisibility of `z`.
The equality holds for every proof of finiteness used in the definition. -/
theorem polynomialBadPrimeModulus_eq_primeRadical_of_bad_iff
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0)
    (G : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hbad : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      (¬ GoodReductionAt p A G ↔ (p : ℤ) ∣ z))
    (hfinite : (badReductionPrimes A G).Finite) :
    polynomialBadPrimeModulus A G hfinite =
      primeRadical (quadraticBadPrimeModulus A * z.natAbs) := by
  rw [polynomialBadPrimeModulus,
    badReductionPrimes_toFinset_eq_primeFactors_sdiff A hdet G z hz hbad hfinite]
  unfold primeRadical
  rw [Nat.primeFactors_mul (quadraticBadPrimeModulus_ne_zero A hdet)
    (Int.natAbs_ne_zero.mpr hz)]
  rw [← Finset.prod_union disjoint_sdiff_self_right, Finset.union_sdiff_self_eq_union]

end QuaternaryQuadraticForms
