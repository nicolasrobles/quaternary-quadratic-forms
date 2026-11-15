import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree

/-!
# A negative Jacobi-symbol value in a fixed residue class

If a squarefree positive modulus has an odd prime divisor, a quadratic
nonresidue at that prime can be combined with the residue one at all
remaining factors and modulo eight. The Chinese remainder theorem
then gives a coprime numerator with Jacobi symbol minus one.
-/

namespace QuaternaryQuadraticForms

/-- A squarefree modulus with an odd prime divisor admits a coprime
Jacobi numerator congruent to one modulo eight with symbol minus one. -/
theorem exists_jacobiSym_neg_one_mod_eight_of_squarefree (s p : ℕ)
    (hs : Squarefree s) (hp : p.Prime) (hp2 : p ≠ 2) (hps : p ∣ s) :
    ∃ n : ℕ, n % 8 = 1 ∧ n.Coprime s ∧ jacobiSym (n : ℤ) s = -1 := by
  obtain ⟨t, rfl⟩ := hps
  have ht : t ≠ 0 := (Nat.mul_ne_zero_iff.mp hs.ne_zero).2
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p * t) := ⟨hs.ne_zero⟩
  have hpt : p.Coprime t := Nat.coprime_of_squarefree_mul hs
  have hp8 : p.Coprime 8 := by
    simpa using ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right 3
  obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one
    (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨n, hnp, hn8t⟩ := Nat.chineseRemainder (hp8.mul_right hpt) r.val 1
  have hn8 : n % 8 = 1 := by
    have h := Nat.ModEq.of_dvd (dvd_mul_right 8 t) hn8t
    change n % 8 = 1 % 8 at h
    exact h
  have hnt : n ≡ 1 [MOD t] := Nat.ModEq.of_dvd (dvd_mul_left t 8) hn8t
  have hjp : jacobiSym (n : ℤ) p = -1 := by
    calc
      _ = jacobiSym (r.val : ℤ) p :=
        jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hnp)
      _ = -1 := by
        rw [← jacobiSym.legendreSym.to_jacobiSym]
        simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using hr
  have hjt : jacobiSym (n : ℤ) t = 1 := by
    calc
      _ = jacobiSym (1 : ℤ) t :=
        jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hnt)
      _ = 1 := jacobiSym.one_left t
  have hjs : jacobiSym (n : ℤ) (p * t) = -1 := by
    rw [jacobiSym.mul_right' _ hp.ne_zero ht, hjp, hjt, mul_one]
  refine ⟨n, hn8, ?_, hjs⟩
  by_contra hnc
  have hz : jacobiSym (n : ℤ) (p * t) = 0 :=
    jacobiSym.eq_zero_iff_not_coprime.mpr (by
      simpa only [Int.gcd_natCast_natCast, Nat.Coprime] using hnc)
  rw [hjs] at hz
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℤ) ≠ 0)) hz

end QuaternaryQuadraticForms
