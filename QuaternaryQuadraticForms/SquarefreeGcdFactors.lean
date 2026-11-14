import Mathlib.Data.Nat.Squarefree

/-!
# The literal squarefree gcd factors in Lemma 3.5

The source factors are `gcd q c` and `q / gcd q c`. Squarefreeness
makes the latter coprime to the whole first CRT block. For a modulus
split into coprime factors, a squarefree divisor splits into its two
actual gcds, and the resulting CRT blocks remain coprime.
-/

namespace QuaternaryQuadraticForms

/-- The source gcd and quotient factors, with every positivity,
squarefreeness, and CRT coprimality conclusion derived from the data. -/
theorem squarefree_gcd_factors (q c : ℕ) (hq : Squarefree q) (hc : c ≠ 0) :
    Nat.gcd q c * (q / Nat.gcd q c) = q ∧
      Nat.gcd q c ≠ 0 ∧ q / Nat.gcd q c ≠ 0 ∧
      Squarefree (Nat.gcd q c) ∧ Squarefree (q / Nat.gcd q c) ∧
      (q / Nat.gcd q c).Coprime (Nat.gcd q c * c) ∧ Nat.gcd q c ∣ c := by
  have hd : Squarefree (Nat.gcd q c) := hq.squarefree_of_dvd (Nat.gcd_dvd_left q c)
  have he : Squarefree (q / Nat.gcd q c) :=
    hq.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q c))
  have hec := Nat.coprime_div_gcd_of_squarefree hq hc
  exact ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left q c), hd.ne_zero, he.ne_zero, hd, he,
    (hec.of_dvd_right (Nat.gcd_dvd_right q c)).mul_right hec, Nat.gcd_dvd_right q c⟩

/-- The source shared factors of two coprime modulus blocks have
coprime full CRT moduli. This deduction does not require squarefreeness. -/
theorem gcd_mul_blocks_coprime (q m n : ℕ) (hmn : m.Coprime n) :
    (Nat.gcd q m * m).Coprime (Nat.gcd q n * n) := by
  exact ((hmn.gcd_both q q).mul_left (hmn.gcd_right q)).mul_right
    ((hmn.gcd_left q).mul_left hmn)

/-- A squarefree divisor of a product of coprime moduli splits into
the actual gcds used in the source's shared-prime factorization. -/
theorem squarefree_shared_gcd_factors (q m n : ℕ) (hq : Squarefree q)
    (hdiv : q ∣ m * n) (hmn : m.Coprime n) :
    Nat.gcd q m * Nat.gcd q n = q ∧
      Squarefree (Nat.gcd q m) ∧ Squarefree (Nat.gcd q n) ∧
      Nat.gcd q m ∣ m ∧ Nat.gcd q n ∣ n ∧
      (Nat.gcd q m * m).Coprime (Nat.gcd q n * n) := by
  exact ⟨(Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr hdiv,
    hq.squarefree_of_dvd (Nat.gcd_dvd_left q m),
    hq.squarefree_of_dvd (Nat.gcd_dvd_left q n),
    Nat.gcd_dvd_right q m, Nat.gcd_dvd_right q n, gcd_mul_blocks_coprime q m n hmn⟩

/-- A squarefree divisor of a prime power is one or that prime,
including the exponent-zero case. -/
theorem squarefree_dvd_prime_pow_eq_one_or_prime (q p k : ℕ)
    (hq : Squarefree q) (hp : p.Prime) (hdiv : q ∣ p ^ k) :
    q = 1 ∨ q = p := by
  by_cases hk : k = 0
  · exact Or.inl (Nat.dvd_one.mp (by simpa only [hk, pow_zero] using hdiv))
  · exact (Nat.dvd_prime hp).mp ((hq.dvd_pow_iff_dvd hk).mp hdiv)

end QuaternaryQuadraticForms
