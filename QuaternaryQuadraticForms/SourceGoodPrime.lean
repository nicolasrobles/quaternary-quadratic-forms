import QuaternaryQuadraticForms.GoodReduction

/-!
# Good primes from the source's radical divisibility condition

Section 3 assumes that `N` contains the radical of the quadratic
bad-prime modulus. For a nonsingular integral matrix, any prime excluded
from `N` is therefore excluded from the actual quadratic bad-prime
modulus. The existing radical is the literal product of distinct prime
divisors; the nonzero determinant hypothesis rules out its empty-product
convention at zero.

The manuscript also assumes `N ≥ 1`. The deduction below is stronger:
the single hypothesis that the selected prime does not divide `N`
already excludes `N = 0`.
-/

namespace QuaternaryQuadraticForms

/-- The source condition `rad(N_F) ∣ N` implies that every prime not
dividing `N` is a good prime for the actual integral quadratic form. -/
theorem source_not_dvd_quadraticBadPrimeModulus
    (N p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hpN : ¬ p ∣ N) :
    ¬ p ∣ quadraticBadPrimeModulus A := by
  intro hpA
  apply hpN
  exact ((prime_dvd_primeRadical_iff p (quadraticBadPrimeModulus A)
    Fact.out (quadraticBadPrimeModulus_ne_zero A hdet)).mpr hpA).trans hrad

end QuaternaryQuadraticForms
