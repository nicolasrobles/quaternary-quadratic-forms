import QuaternaryQuadraticForms.ModulusPrimeSplit
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Ring

/-!
# The actual totient and the relative Möbius divisor expansion

Möbius inversion of the ordinary totient divisor sum gives an integral
formula. Separating the part of an integer supported on the primes of
the fixed factor gives the relative formula used in Lemma 3.7. Keeping
the quotient integral makes subsequent finite reindexing denominator-free.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Möbius inversion of the actual totient divisor sum, in any
commutative ring and including the zero argument. -/
theorem totient_eq_sum_moebius {R : Type*} [CommRing R] (n : ℕ) :
    (n.totient : R) =
      ∑ h ∈ n.divisors, (ArithmeticFunction.moebius h : R) * ((n / h : ℕ) : R) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hsum : ∀ (m : ℕ), 0 < m → ∑ h ∈ m.divisors, (h.totient : R) = (m : R) := by
    intro m _
    simpa only [Nat.cast_sum] using congrArg (fun k : ℕ => (k : R)) (Nat.sum_totient m)
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum n
    (Nat.pos_of_ne_zero hn)
  rw [Nat.sum_divisorsAntidiagonal
    (fun h k : ℕ => (ArithmeticFunction.moebius h : R) * (k : R))] at hinv
  exact hinv.symm

private theorem totient_mul_of_prime_support (d b : ℕ) (hd : d ≠ 0) (hb : b ≠ 0)
    (hbd : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ d) :
    (d * b).totient = b * d.totient := by
  have hsub : b.primeFactors ⊆ d.primeFactors := by
    intro p hp
    have hmem := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hmem.1, hbd p hmem.1 hmem.2.1, hd⟩
  have hfactors : (d * b).primeFactors = d.primeFactors := by
    rw [Nat.primeFactors_mul hd hb, Finset.union_eq_left.mpr hsub]
  have hrat : ((d * b).totient : ℚ) = (b : ℚ) * (d.totient : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors, hfactors, Nat.totient_eq_mul_prod_factors]
    push_cast
    ring
  exact_mod_cast hrat

/-- The relative totient expansion with the literal coprimality
restriction on divisors. No squarefreeness assumption is needed. -/
theorem totient_mul_eq_sum_moebius {R : Type*} [CommRing R]
    (d n : ℕ) (hd : d ≠ 0) :
    ((d * n).totient : R) = (d.totient : R) *
      ∑ h ∈ n.divisors, if h.Coprime d then
        (ArithmeticFunction.moebius h : R) * ((n / h : ℕ) : R) else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  obtain ⟨b, g, hb, hg, hng, hbg, hgd, hbd⟩ := exists_modulus_prime_split n d hn
  have hdbg : (d * b).Coprime g := hgd.symm.mul_left hbg
  have hphi : (d * n).totient = d.totient * b * g.totient := by
    rw [hng, ← Nat.mul_assoc, Nat.totient_mul hdbg,
      totient_mul_of_prime_support d b hd hb hbd]
    ring
  have hdivisors : n.divisors.filter (fun h => h.Coprime d) = g.divisors := by
    ext h
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hhn, hhd⟩
      have hhdiv := Nat.dvd_of_mem_divisors hhn
      have hhb : h.Coprime b := coprime_of_prime_dvd_support h b d hhd hbd
      rw [hng] at hhdiv
      exact Nat.mem_divisors.mpr ⟨hhb.dvd_mul_left.mp hhdiv, hg⟩
    · intro hhg
      have hhdiv := Nat.dvd_of_mem_divisors hhg
      have hgn : g ∣ n := ⟨b, by simpa only [Nat.mul_comm] using hng⟩
      exact ⟨Nat.mem_divisors.mpr ⟨hhdiv.trans hgn, hn⟩, hgd.of_dvd_left hhdiv⟩
  calc
    _ = (d.totient : R) * (b : R) * (g.totient : R) := by
      simp only [hphi, Nat.cast_mul]
    _ = (d.totient : R) *
        ∑ h ∈ g.divisors, (ArithmeticFunction.moebius h : R) * ((n / h : ℕ) : R) := by
      rw [totient_eq_sum_moebius (R := R) g, mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      rw [hng, Nat.mul_div_assoc b (Nat.dvd_of_mem_divisors hh), Nat.cast_mul]
      ring
    _ = _ := by rw [← hdivisors, Finset.sum_filter]

end QuaternaryQuadraticForms
