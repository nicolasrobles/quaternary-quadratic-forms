import QuaternaryQuadraticForms.ModulusNormSum
import QuaternaryQuadraticForms.ModulusPrimeSplit
import QuaternaryQuadraticForms.PrimeSupportCount
import QuaternaryQuadraticForms.CompleteSumFactorization
import QuaternaryQuadraticForms.GoodPrime
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact factorization of the sum over moduli

The bad-supported and good factors form a genuine finite bijection.
This preserves cancellation within each good-modulus sum before any
norm is taken. The actual complete sum is extended only at modulus zero,
which is absent from every summation set.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A factor supported on `N` and a factor coprime to `N` are uniquely
determined by their positive product. -/
theorem modulus_prime_split_unique (N b g b' g' : ℕ) (hb : 0 < b)
    (hbN : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ N)
    (hbN' : ∀ p : ℕ, p.Prime → p ∣ b' → p ∣ N)
    (hgN : g.Coprime N) (hgN' : g'.Coprime N)
    (hprod : b * g = b' * g') : b = b' ∧ g = g' := by
  have hbg' := (coprime_of_prime_dvd_support g' b N hgN' hbN).symm
  have hb'g := (coprime_of_prime_dvd_support g b' N hgN hbN').symm
  have hbb' : b ∣ b' := hbg'.dvd_of_dvd_mul_right
    (hprod ▸ dvd_mul_right b g)
  have hb'b : b' ∣ b := hb'g.dvd_of_dvd_mul_right
    (hprod.symm ▸ dvd_mul_right b' g')
  have heq := Nat.dvd_antisymm hbb' hb'b
  refine ⟨heq, ?_⟩
  subst b'
  exact Nat.eq_of_mul_eq_mul_left hb hprod

/-- The exact finite bad/good factorization, retaining the literal gcd
restriction and divided cutoff. -/
theorem sum_gcdModuli_eq_sum_prime_split (q d N T : ℕ)
    (hqN : q.Coprime N) (f : ℕ → ℂ) :
    (∑ c ∈ gcdModuliUpTo q d T, f c) =
      ∑ b ∈ primeSupportModuliUpTo N T,
        ∑ g ∈ (gcdModuliUpTo q d (T / b)).filter (fun g => g.Coprime N), f (b * g) := by
  classical
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun x _ => x.1 * x.2)
  · intro x hx
    obtain ⟨hb, hg⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hbpos, _, hbN⟩ := (mem_primeSupportModuliUpTo N T x.1).mp hb
    obtain ⟨hg, hgN⟩ := Finset.mem_filter.mp hg
    obtain ⟨hgpos, hgle, hggcd⟩ := (mem_gcdModuliUpTo q d (T / x.1) x.2).mp hg
    refine (mem_gcdModuliUpTo q d T (x.1 * x.2)).mpr
      ⟨Nat.mul_pos hbpos hgpos, ?_, ?_⟩
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hbpos).mp hgle
    · rw [Nat.gcd_comm, gcd_eq_good_part_of_prime_support q (x.1 * x.2)
        x.1 x.2 N hqN rfl hbN, Nat.gcd_comm]
      exact hggcd
  · intro x hx y hy hxy
    obtain ⟨hbx, hgx⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hby, hgy⟩ := Finset.mem_sigma.mp hy
    have hbx' := (mem_primeSupportModuliUpTo N T x.1).mp hbx
    have hby' := (mem_primeSupportModuliUpTo N T y.1).mp hby
    obtain ⟨hb, hg⟩ := modulus_prime_split_unique N x.1 x.2 y.1 y.2
      hbx'.1 hbx'.2.2 hby'.2.2 (Finset.mem_filter.mp hgx).2
      (Finset.mem_filter.mp hgy).2 hxy
    exact Sigma.ext hb (heq_of_eq hg)
  · intro c hc
    obtain ⟨hcpos, hcle, hcgcd⟩ := (mem_gcdModuliUpTo q d T c).mp hc
    obtain ⟨b, g, hb, hg, hprod, _, hgN, hbN⟩ :=
      exists_modulus_prime_split c N (Nat.ne_of_gt hcpos)
    refine ⟨⟨b, g⟩, ?_, hprod.symm⟩
    apply Finset.mem_sigma.mpr
    refine ⟨(mem_primeSupportModuliUpTo N T b).mpr
      ⟨Nat.pos_of_ne_zero hb, ?_, hbN⟩, ?_⟩
    · exact (Nat.le_of_dvd hcpos (hprod ▸ dvd_mul_right b g)).trans hcle
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_gcdModuliUpTo q d (T / b) g).mpr
        ⟨Nat.pos_of_ne_zero hg, ?_, ?_⟩, hgN⟩
      · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).mpr
        simpa only [Nat.mul_comm, ← hprod] using hcle
      · rw [Nat.gcd_comm, ← gcd_eq_good_part_of_prime_support q c b g N hqN hprod hbN,
          Nat.gcd_comm]
        exact hcgcd
  · intro _ _
    rfl

/-- The actual unweighted complete sum at positive moduli, extended by
zero solely to provide a total function on natural numbers. -/
def unweightedCompleteSumValue (c : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (u : Fin 4 → ℤ) : ℂ :=
  if hc : c = 0 then 0 else
    letI : NeZero c := ⟨hc⟩
    unweightedCompleteSum c A u

/-- At each positive modulus the total summand equals the source sum. -/
theorem unweightedCompleteSumValue_of_neZero (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    unweightedCompleteSumValue c A u = unweightedCompleteSum c A u := by
  simp only [unweightedCompleteSumValue, dif_neg (NeZero.ne c)]

/-- The actual complex modulus sum with a real cutoff and exact gcd
condition; its norm is taken only after the summation. -/
def unweightedModulusSum (q d : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (u : Fin 4 → ℤ) (X : ℝ) : ℂ :=
  ∑ c ∈ gcdModuliUpTo q d ⌊X⌋₊, unweightedCompleteSumValue c A u

/-- Exact CRT factorization of the actual modulus sum, with all
cancellation inside each good-modulus sum preserved. -/
theorem unweightedModulusSum_prime_split (q d : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hqN : q.Coprime (quadraticBadPrimeModulus A)) (X : ℝ) :
    unweightedModulusSum q d A u X =
      ∑ b ∈ primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊,
        unweightedCompleteSumValue b A u *
          ∑ g ∈ (gcdModuliUpTo q d (⌊X⌋₊ / b)).filter
            (fun g => g.Coprime (quadraticBadPrimeModulus A)),
              unweightedCompleteSumValue g A u := by
  classical
  rw [unweightedModulusSum, sum_gcdModuli_eq_sum_prime_split q d
    (quadraticBadPrimeModulus A) ⌊X⌋₊ hqN]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨hbpos, _, hbN⟩ :=
    (mem_primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊ b).mp hb
  letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hgmem := Finset.mem_filter.mp hg
  have hgpos := ((mem_gcdModuliUpTo q d (⌊X⌋₊ / b) g).mp hgmem.1).1
  letI : NeZero g := ⟨Nat.ne_of_gt hgpos⟩
  rw [unweightedCompleteSumValue_of_neZero, unweightedCompleteSumValue_of_neZero,
    unweightedCompleteSumValue_of_neZero, unweightedCompleteSum_mul]
  exact (coprime_of_prime_dvd_support g b (quadraticBadPrimeModulus A) hgmem.2 hbN).symm

end QuaternaryQuadraticForms
