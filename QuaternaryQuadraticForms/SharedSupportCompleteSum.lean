import QuaternaryQuadraticForms.GoodUnweightedCompleteSum
import QuaternaryQuadraticForms.RamifiedCompleteSum
import QuaternaryQuadraticForms.CompleteSumCRT
import QuaternaryQuadraticForms.SquarefreeGcdFactors
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The complete sum when every weight prime divides the modulus

For a squarefree divisor `q` of a good modulus `c`, the actual mixed
sum is assembled from the unramified and ramified prime-power formulas.
Induction over positive coprime modulus factors uses the literal gcds
to split `q`; the proved CRT identity, character, composite weights,
and actual Ramanujan sums then give the complete source coefficient.
-/

noncomputable section

namespace QuaternaryQuadraticForms

private theorem shared_primeWeightsInvariant_of_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d : ℕ) [NeZero q] (hd : d ∣ q) (hξ : PrimeWeightsInvariant ξ q) :
    PrimeWeightsInvariant ξ d := by
  intro p hp
  exact hξ p (Nat.primeFactors_mono hd (NeZero.ne q) hp)

private theorem mixedCompleteSum_shared_support_all
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (u : Fin 4 → ℤ) :
    ∀ c : ℕ, ∀ [NeZero c], ∀ q : ℕ, ∀ [NeZero q],
      Squarefree q → q ∣ c → c.Coprime (quadraticBadPrimeModulus A) →
      PrimeWeightsInvariant ξ q →
      mixedCompleteSum ξ q c A u =
        (q : ℂ) * (c : ℂ) ^ 2 * globalQuadraticChar A.det (q * c) *
          compositeWeight ξ q (A.adjugate.mulVec u) *
            integralRamanujanSum (q * c) (dotProduct u (A.adjugate.mulVec u)) := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p k hp hk _ q _ hq hqc hc hξ
    letI : Fact p.Prime := ⟨hp⟩
    rcases squarefree_dvd_prime_pow_eq_one_or_prime q p k hq hp hqc with hqone | hqprime
    · subst q
      rw [mixedCompleteSum_one_left, unweightedCompleteSum_good_modulus (p ^ k) A hA hc u]
      simp only [Nat.cast_one, one_mul, compositeWeight_one, mul_one]
      ring
    · subst q
      have hpgood : ¬ p ∣ quadraticBadPrimeModulus A :=
        hp.coprime_iff_not_dvd.mp (hc.of_dvd_left (dvd_pow_self p hk.ne'))
      have hξp : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p,
          ξ p (r • y) = ξ p y :=
        hξ p (by simp [hp.primeFactors])
      rw [ramified_complete_sum p k hk ξ hξp A hA hpgood u]
      simp only [← pow_succ' p k, globalQuadraticChar_prime_power,
        compositeWeight_prime ξ p hp, Nat.cast_pow]
      rw [← pow_mul, show 2 * k + 1 = k * 2 + 1 by omega, pow_succ]
      unfold reduceFrequency
      ring
  · intro _ q _ hq hqc hc hξ
    exact (NeZero.ne 0 rfl).elim
  · intro _ q _ hq hqc hc hξ
    have hq1 : q = 1 := Nat.dvd_one.mp hqc
    subst q
    simp only [mixedCompleteSum_one_one, Nat.cast_one, one_mul, one_pow,
      globalQuadraticChar_one, compositeWeight_one, integralRamanujanSum_modulus_one]
  · intro m n hm hn hmn ihm ihn _ q _ hq hqc hc hξ
    letI : NeZero m := ⟨by omega⟩
    letI : NeZero n := ⟨by omega⟩
    let q₁ := Nat.gcd q m
    let q₂ := Nat.gcd q n
    obtain ⟨hprod, hsq₁, hsq₂, hd₁, hd₂, hblocks⟩ :=
      squarefree_shared_gcd_factors q m n hq hqc hmn
    change q₁ * q₂ = q at hprod
    change Squarefree q₁ at hsq₁
    change Squarefree q₂ at hsq₂
    change q₁ ∣ m at hd₁
    change q₂ ∣ n at hd₂
    change (q₁ * m).Coprime (q₂ * n) at hblocks
    letI : NeZero q₁ := ⟨hsq₁.ne_zero⟩
    letI : NeZero q₂ := ⟨hsq₂.ne_zero⟩
    have hξ₁ : PrimeWeightsInvariant ξ q₁ :=
      shared_primeWeightsInvariant_of_dvd ξ q q₁ (Nat.gcd_dvd_left q m) hξ
    have hξ₂ : PrimeWeightsInvariant ξ q₂ :=
      shared_primeWeightsInvariant_of_dvd ξ q q₂ (Nat.gcd_dvd_left q n) hξ
    have hξprod : PrimeWeightsInvariant ξ (q₁ * q₂) := by
      simpa only [hprod] using hξ
    have hm_good : m.Coprime (quadraticBadPrimeModulus A) :=
      hc.of_dvd_left (dvd_mul_right m n)
    have hn_good : n.Coprime (quadraticBadPrimeModulus A) :=
      hc.of_dvd_left (dvd_mul_left n m)
    have hcrt : mixedCompleteSum ξ q (m * n) A u =
        mixedCompleteSum ξ q₁ m A u * mixedCompleteSum ξ q₂ n A u := by
      simpa only [hprod] using mixedCompleteSum_crt ξ q₁ q₂ m n A u hblocks hξprod
    have hmod : q * (m * n) = (q₁ * m) * (q₂ * n) := by
      calc
        q * (m * n) = (q₁ * q₂) * (m * n) :=
          congrArg (fun d => d * (m * n)) hprod.symm
        _ = _ := by ring
    have hqq : q₁.Coprime q₂ := (hmn.of_dvd_left hd₁).of_dvd_right hd₂
    have hweight : compositeWeight ξ q (A.adjugate.mulVec u) =
        compositeWeight ξ q₁ (A.adjugate.mulVec u) *
          compositeWeight ξ q₂ (A.adjugate.mulVec u) := by
      calc
        _ = compositeWeight ξ (q₁ * q₂) (A.adjugate.mulVec u) :=
          congrArg (fun d => compositeWeight ξ d (A.adjugate.mulVec u)) hprod.symm
        _ = _ := compositeWeight_mul ξ q₁ q₂ hqq (A.adjugate.mulVec u)
    have hqcast : (q : ℂ) = (q₁ : ℂ) * (q₂ : ℂ) := by
      exact_mod_cast hprod.symm
    rw [hcrt, ihm q₁ hsq₁ hd₁ hm_good hξ₁, ihn q₂ hsq₂ hd₂ hn_good hξ₂]
    simp only [hmod]
    rw [globalQuadraticChar_mul A.det (q₁ * m) (q₂ * n),
      integralRamanujanSum_mul (q₁ * m) (q₂ * n) hblocks,
      hweight, hqcast, Nat.cast_mul]
    ring

/-- The source closed formula for every squarefree `q ∣ c` at a good
positive modulus, with the actual local weights and every integral frequency. -/
theorem mixedCompleteSum_shared_support
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q) (hqc : q ∣ c)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ q c A u =
      (q : ℂ) * (c : ℂ) ^ 2 * globalQuadraticChar A.det (q * c) *
        compositeWeight ξ q (A.adjugate.mulVec u) *
          integralRamanujanSum (q * c) (dotProduct u (A.adjugate.mulVec u)) :=
  mixedCompleteSum_shared_support_all ξ A hA u c q hq hqc hc hξ

end QuaternaryQuadraticForms
