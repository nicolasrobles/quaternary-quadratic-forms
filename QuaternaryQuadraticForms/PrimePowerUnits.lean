import QuaternaryQuadraticForms.GoodPrime
import QuaternaryQuadraticForms.CompleteSumAlgebra

/-!
# The source good-prime hypotheses at every prime power

Nondivisibility by a prime supplies the actual units needed for square
completion at all its powers. The excluded modulus is exactly `2 |det A|`.
-/

namespace QuaternaryQuadraticForms

/-- An integer not divisible by a prime is a unit modulo every power of that prime. -/
theorem intCast_isUnit_prime_pow (p k : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ k)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hcop : IsCoprime (p : ℤ) a := hp.coprime_iff_not_dvd.mpr ha
  simpa only [Nat.cast_pow] using (hcop.pow_left (m := k))

/-- At a source good prime, the determinant is not divisible by that prime. -/
theorem goodPrime_not_dvd_det (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) : ¬ (p : ℤ) ∣ A.det := by
  intro h
  apply hp
  exact dvd_mul_of_dvd_right
    (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h)) 2

/-- The source good-prime condition makes two a unit at every prime power. -/
theorem goodPrime_two_isUnit_prime_pow (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hp : ¬ p ∣ quadraticBadPrimeModulus A) :
    IsUnit (2 : ZMod (p ^ k)) := by
  have htwo : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    have hnat : p ∣ 2 := by exact_mod_cast h
    exact goodPrime_ne_two p A hp ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) Nat.prime_two).mp hnat)
  simpa only [Int.cast_ofNat] using intCast_isUnit_prime_pow p k 2 htwo

/-- The reduced determinant is a unit modulo every power of a source good prime. -/
theorem goodPrime_det_isUnit_prime_pow (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hp : ¬ p ∣ quadraticBadPrimeModulus A) :
    IsUnit (reduceQuadraticMatrix (p ^ k) A).det := by
  have h := intCast_isUnit_prime_pow p k A.det (goodPrime_not_dvd_det p A hp)
  have heq : (A.det : ZMod (p ^ k)) = (reduceQuadraticMatrix (p ^ k) A).det :=
    (Int.castRingHom (ZMod (p ^ k))).map_det A
  exact heq ▸ h

end QuaternaryQuadraticForms
