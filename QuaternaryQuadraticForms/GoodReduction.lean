import QuaternaryQuadraticForms.GoodPrime
import QuaternaryQuadraticForms.TransversalityRank
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The good-reduction modulus

The bad primes are defined by the literal geometric rank condition. The
modulus is the radical of `N_F` multiplied by the product of that exact set.
Its definition takes a proof that the bad-prime set is finite; no finiteness
claim is assumed as an axiom. The arithmetic results here isolate the part
of the reduction argument that follows once that proof has been supplied.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The two-gradient rank condition for the actual projective intersection. -/
def ProjectiveIntersectionTransverseRank {N : ℕ} {K : Type*} [Field K]
    (F G : MvPolynomial (Fin N) K) : Prop :=
  ∀ x : Fin N → K, x ≠ 0 → MvPolynomial.eval x F = 0 →
    MvPolynomial.eval x G = 0 →
      Matrix.rank ![polynomialGradient F x, polynomialGradient G x] = 2

/-- The rank-two condition is exactly independence of the two actual rows. -/
theorem rank_two_iff_linearIndependent {N : ℕ} {K : Type*} [Field K]
    (v : Fin 2 → Fin N → K) :
    Matrix.rank v = 2 ↔ LinearIndependent K v := by
  rw [linearIndependent_iff_card_eq_finrank_span,
    Matrix.rank_eq_finrank_span_row]
  change Module.finrank K (Submodule.span K (Set.range v)) = 2 ↔
    2 = Module.finrank K (Submodule.span K (Set.range v))
  exact eq_comm

/-- The literal geometric rank condition is equivalent to independence of
the evaluated gradient vectors at every nonzero common zero. -/
theorem projectiveIntersectionTransverseRank_iff {N : ℕ} {K : Type*} [Field K]
    (F G : MvPolynomial (Fin N) K) :
    ProjectiveIntersectionTransverseRank F G ↔
      ∀ x : Fin N → K, x ≠ 0 → MvPolynomial.eval x F = 0 →
        MvPolynomial.eval x G = 0 →
          LinearIndependent K ![polynomialGradient F x, polynomialGradient G x] := by
  constructor
  · intro h x hx hF hG
    exact (rank_two_iff_linearIndependent _).mp (h x hx hF hG)
  · intro h x hx hF hG
    exact (rank_two_iff_linearIndependent _).mpr (h x hx hF hG)

/-- Good reduction of the actual integral equations at a prime, expressed
by the manuscript's rank condition over the algebraic closure. -/
def GoodReductionAt (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ) : Prop :=
  ProjectiveIntersectionTransverseRank
    ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
    ((G.map (Int.castRingHom (ZMod p))).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))

/-- The exact primes occurring in the additional product defining `N_G`. -/
def badReductionPrimes (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) : Set ℕ :=
  {p | ∃ hp : p.Prime, ¬ p ∣ quadraticBadPrimeModulus A ∧
    ¬ @GoodReductionAt p ⟨hp⟩ A G}

/-- For a prime, membership in the bad-prime set is exactly bad reduction
away from the quadratic bad-prime modulus. -/
theorem mem_badReductionPrimes (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ) :
    p ∈ badReductionPrimes A G ↔
      ¬ p ∣ quadraticBadPrimeModulus A ∧ ¬ GoodReductionAt p A G := by
  constructor
  · rintro ⟨_, hF, hG⟩
    exact ⟨hF, hG⟩
  · rintro ⟨hF, hG⟩
    exact ⟨Fact.out, hF, hG⟩

/-- The radical as the product of the distinct prime divisors. -/
def primeRadical (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors, p

/-- The literal finite product in the manuscript's definition of `N_G`. -/
def polynomialBadPrimeModulus (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) (hfinite : (badReductionPrimes A G).Finite) : ℕ :=
  primeRadical (quadraticBadPrimeModulus A) * ∏ p ∈ hfinite.toFinset, p

/-- A prime divides the radical of a nonzero natural number exactly when it
divides that number. -/
theorem prime_dvd_primeRadical_iff (p N : ℕ) (hp : p.Prime) (hN : N ≠ 0) :
    p ∣ primeRadical N ↔ p ∣ N := by
  constructor
  · intro h
    exact h.trans (Nat.prod_primeFactors_dvd N)
  · intro h
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q)
      ((Nat.mem_primeFactors_of_ne_zero hN).mpr ⟨hp, h⟩)

/-- The radical product is positive, including at zero under the library's
empty prime-factor convention. The manuscript uses it only for nonzero `N_F`. -/
theorem primeRadical_pos (N : ℕ) : 0 < primeRadical N := by
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

/-- A nonsingular integral matrix has a nonzero quadratic bad-prime modulus. -/
theorem quadraticBadPrimeModulus_ne_zero (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hdet : A.det ≠ 0) : quadraticBadPrimeModulus A ≠ 0 := by
  exact mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hdet)

/-- The actual finite bad-prime product is a positive integer. -/
theorem polynomialBadPrimeModulus_pos (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) (hfinite : (badReductionPrimes A G).Finite) :
    0 < polynomialBadPrimeModulus A G hfinite := by
  apply Nat.mul_pos (primeRadical_pos _)
  apply Finset.prod_pos
  intro p hp
  obtain ⟨hprime, _, _⟩ := hfinite.mem_toFinset.mp hp
  exact hprime.pos

/-- A prime divides a finite product of distinct primes exactly when it is
one of its factors. -/
theorem prime_dvd_product_primes_iff (p : ℕ) (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) :
    p ∣ ∏ q ∈ s, q ↔ p ∈ s := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := hp.prime.dvd_finset_prod_iff (fun q : ℕ => q) |>.mp h
    rcases (Nat.dvd_prime (hs q hq)).mp hpq with h1 | heq
    · exact False.elim (hp.ne_one h1)
    · exact heq ▸ hq
  · intro h
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) h

/-- Excluding the actual `N_G` is equivalent to excluding `N_F` and having
the literal geometric good-reduction property. Finiteness is an explicit
proved-data argument, not a replacement premise for its elimination proof. -/
theorem not_dvd_polynomialBadPrimeModulus_iff (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0)
    (G : MvPolynomial (Fin 4) ℤ) (hfinite : (badReductionPrimes A G).Finite) :
    ¬ p ∣ polynomialBadPrimeModulus A G hfinite ↔
      ¬ p ∣ quadraticBadPrimeModulus A ∧ GoodReductionAt p A G := by
  have hp : p.Prime := Fact.out
  have hproduct : p ∣ ∏ q ∈ hfinite.toFinset, q ↔ p ∈ badReductionPrimes A G := by
    rw [prime_dvd_product_primes_iff p hp]
    · exact hfinite.mem_toFinset
    · intro q hq
      exact (hfinite.mem_toFinset.mp hq).choose
  rw [polynomialBadPrimeModulus, hp.dvd_mul,
    prime_dvd_primeRadical_iff p _ hp (quadraticBadPrimeModulus_ne_zero A hdet),
    hproduct, mem_badReductionPrimes]
  tauto

/-- A nonzero integer divisible by every bad prime contains the exact
bad-prime set among its prime divisors. -/
theorem badReductionPrimes_subset_primeFactors_of_common_divisor
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (z : ℤ) (hz : z ≠ 0)
    (hdiv : ∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z) :
    badReductionPrimes A G ⊆ (↑z.natAbs.primeFactors : Set ℕ) := by
  intro p hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp.choose, ?_, Int.natAbs_ne_zero.mpr hz⟩
  exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (hdiv p hp))

/-- The arithmetic finiteness deduction used after elimination supplies a
single nonzero integer divisible by every bad prime. -/
theorem badReductionPrimes_finite_of_common_divisor
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (z : ℤ) (hz : z ≠ 0)
    (hdiv : ∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z) :
    (badReductionPrimes A G).Finite :=
  (Set.toFinite (↑z.natAbs.primeFactors : Set ℕ)).subset
    (badReductionPrimes_subset_primeFactors_of_common_divisor A G z hz hdiv)

/-- The product of the actual bad primes divides any nonzero integer that
is divisible by each of them. -/
theorem badReductionPrimeProduct_dvd_common_divisor
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (hfinite : (badReductionPrimes A G).Finite) (z : ℤ) (hz : z ≠ 0)
    (hdiv : ∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z) :
    (∏ p ∈ hfinite.toFinset, p) ∣ z.natAbs := by
  apply dvd_trans (Finset.prod_dvd_prod_of_subset
    hfinite.toFinset z.natAbs.primeFactors (fun q : ℕ => q) ?_)
    (Nat.prod_primeFactors_dvd z.natAbs)
  intro p hp
  exact badReductionPrimes_subset_primeFactors_of_common_divisor A G z hz hdiv
    (hfinite.mem_toFinset.mp hp)

/-- The resulting modulus bound before the elimination value is bounded in
terms of the coefficient height. -/
theorem polynomialBadPrimeModulus_le_of_common_divisor
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (hfinite : (badReductionPrimes A G).Finite) (z : ℤ) (hz : z ≠ 0)
    (hdiv : ∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z) :
    polynomialBadPrimeModulus A G hfinite ≤
      primeRadical (quadraticBadPrimeModulus A) * z.natAbs := by
  apply Nat.mul_le_mul_left
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hz))
    (badReductionPrimeProduct_dvd_common_divisor A G hfinite z hz hdiv)

end QuaternaryQuadraticForms
