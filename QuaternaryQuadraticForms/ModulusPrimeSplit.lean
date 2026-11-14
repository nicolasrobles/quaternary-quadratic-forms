import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.Basic

/-!
# Separating a modulus by its actual prime support

Every positive modulus is a product of two coprime positive factors:
all primes of the first divide a specified integer, and the second
is coprime to that integer. The witnesses are constructed by the
proved prime-power induction principle. No factorization is assumed.

The last two deductions show that a modulus coprime to the specified
integer is coprime to the first factor, and that removing that factor
preserves the literal gcd used in Lemma 3.5.
-/

namespace QuaternaryQuadraticForms

/-- A positive modulus admits the source's bad-prime/good-prime split,
with actual positive factors, their coprimality, and their prime support. -/
theorem exists_modulus_prime_split (c N : ℕ) (hc : c ≠ 0) :
    ∃ b g : ℕ, b ≠ 0 ∧ g ≠ 0 ∧ c = b * g ∧ b.Coprime g ∧ g.Coprime N ∧
      (∀ p : ℕ, p.Prime → p ∣ b → p ∣ N) := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun c => c ≠ 0 →
      ∃ b g : ℕ, b ≠ 0 ∧ g ≠ 0 ∧ c = b * g ∧ b.Coprime g ∧ g.Coprime N ∧
        (∀ p : ℕ, p.Prime → p ∣ b → p ∣ N)) ?_ ?_ ?_ ?_ c hc
  · intro p k hp _ _
    by_cases hpN : p ∣ N
    · refine ⟨p ^ k, 1, pow_ne_zero k hp.ne_zero, one_ne_zero, by simp,
        Nat.coprime_one_right _, Nat.coprime_one_left _, ?_⟩
      intro r hr hrd
      have hrp : r = p := (Nat.dvd_prime hp).mp (hr.dvd_of_dvd_pow hrd) |>.resolve_left hr.ne_one
      exact hrp ▸ hpN
    · refine ⟨1, p ^ k, one_ne_zero, pow_ne_zero k hp.ne_zero, by simp,
        Nat.coprime_one_left _, (hp.coprime_iff_not_dvd.mpr hpN).pow_left k, ?_⟩
      intro r hr hrd
      exact (hr.ne_one (Nat.dvd_one.mp hrd)).elim
  · intro hzero
    exact (hzero rfl).elim
  · intro _
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by simp,
      Nat.coprime_one_left _, Nat.coprime_one_left _, ?_⟩
    intro p hp hpone
    exact (hp.ne_one (Nat.dvd_one.mp hpone)).elim
  · intro m n hm hn hmn hmSplit hnSplit _
    obtain ⟨b₁, g₁, hb₁, hg₁, hmg, hbg₁, hgN₁, hbN₁⟩ :=
      hmSplit (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hm))
    obtain ⟨b₂, g₂, hb₂, hg₂, hng, hbg₂, hgN₂, hbN₂⟩ :=
      hnSplit (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))
    have hb₁m : b₁ ∣ m := by rw [hmg]; exact dvd_mul_right b₁ g₁
    have hg₁m : g₁ ∣ m := by rw [hmg]; exact dvd_mul_left g₁ b₁
    have hb₂n : b₂ ∣ n := by rw [hng]; exact dvd_mul_right b₂ g₂
    have hg₂n : g₂ ∣ n := by rw [hng]; exact dvd_mul_left g₂ b₂
    have hcross₁ : b₁.Coprime g₂ := (hmn.of_dvd_left hb₁m).of_dvd_right hg₂n
    have hcross₂ : b₂.Coprime g₁ := (hmn.symm.of_dvd_left hb₂n).of_dvd_right hg₁m
    refine ⟨b₁ * b₂, g₁ * g₂, mul_ne_zero hb₁ hb₂, mul_ne_zero hg₁ hg₂, ?_,
      (hbg₁.mul_left hcross₂).mul_right (hcross₁.mul_left hbg₂),
      hgN₁.mul_left hgN₂, ?_⟩
    · rw [hmg, hng]
      ac_rfl
    · intro p hp hpd
      exact (hp.dvd_mul.mp hpd).elim (hbN₁ p hp) (hbN₂ p hp)

/-- Coprimality with the excluded-prime integer passes to every positive
or zero integer whose prime support lies in that integer's support. -/
theorem coprime_of_prime_dvd_support (q b N : ℕ) (hqN : q.Coprime N)
    (hbN : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ N) : q.Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpq hpb
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpq (hbN p hp hpb) hqN

/-- Removing the factor supported on excluded primes preserves the
actual gcd defining the source's shared squarefree factor. -/
theorem gcd_eq_good_part_of_prime_support (q c b g N : ℕ)
    (hqN : q.Coprime N) (hcg : c = b * g)
    (hbN : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ N) :
    Nat.gcd q c = Nat.gcd q g := by
  rw [hcg]
  exact (coprime_of_prime_dvd_support q b N hqN hbN).symm.gcd_mul_left_cancel_right g

end QuaternaryQuadraticForms
