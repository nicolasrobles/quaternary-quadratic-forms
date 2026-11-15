import QuaternaryQuadraticForms.PolynomialBoxInduction
import QuaternaryQuadraticForms.PolynomialBoxIntervals
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Complete source theorem for Lemma 2.4

The source endpoint takes an independent polynomial only at each prime
dividing the positive squarefree modulus, and arbitrary real intervals.
Their finite integer-point sets are counted literally. The constant is
the exact sum of powers in the manuscript, and the exponent is the usual
number of distinct prime divisors.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The prime-set cardinality is the usual number of distinct prime factors. -/
theorem polynomialBox_primeFactors_card_eq_omega (m : ℕ) :
    m.primeFactors.card = ArithmeticFunction.cardDistinctFactors m := by
  simp only [Nat.primeFactors, List.card_toFinset, ArithmeticFunction.cardDistinctFactors_apply]

/-- The finite-prime-set bound specialized to the actual positive squarefree modulus. -/
theorem polynomialBox_squarefree_card_le (n E m : ℕ) (hn : 1 ≤ n) (hE : 1 ≤ E)
    (_hm : 1 ≤ m) (hsq : Squarefree m)
    (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p))
    (hP : ∀ p ∈ m.primeFactors, P p ≠ 0)
    (hdeg : ∀ p ∈ m.primeFactors, (P p).totalDegree ≤ E)
    (a b : Fin n → ℤ) (Y : ℝ) (hY : 1 ≤ Y)
    (hI : ∀ i, ((Finset.Icc (a i) (b i)).card : ℝ) ≤ Y) :
    ((polynomialBoxSolutions m.primeFactors P a b).card : ℝ) ≤
      (polynomialBoxConstant n E : ℝ) ^ m.primeFactors.card *
        (Y ^ n / (m : ℝ) + Y ^ (n - 1)) := by
  have hb := polynomialBox_primeSet_card_le n E hn hE m.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) P hP hdeg a b Y hY hI
  have hprod : (∏ p ∈ m.primeFactors, (p : ℝ)) = (m : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rwa [hprod] at hb

/-- Extend the polynomial data by zero away from their actual source domain.
The extension is used only to invoke the finite-prime-set helper. -/
def extendPolynomialBoxFamily {n : ℕ} (m : ℕ)
    (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) → MvPolynomial (Fin n) (ZMod p.val))
    (p : ℕ) : MvPolynomial (Fin n) (ZMod p) := by
  classical
  exact if hp : p.Prime ∧ p ∣ m then P ⟨p, hp⟩ else 0

/-- The extension preserves every supplied prime polynomial exactly. -/
theorem extendPolynomialBoxFamily_apply {n : ℕ} (m : ℕ)
    (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) → MvPolynomial (Fin n) (ZMod p.val))
    (p : {p : ℕ // p.Prime ∧ p ∣ m}) :
    extendPolynomialBoxFamily m P p.val = P p := by
  classical
  simp only [extendPolynomialBoxFamily, dif_pos p.property]

/-- The literal set appearing in Lemma 2.4: integer tuples in the given
real intervals, satisfying the independently supplied prime congruences. -/
def sourcePolynomialBoxSet {n : ℕ} (m : ℕ)
    (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) → MvPolynomial (Fin n) (ZMod p.val))
    (I : Fin n → Set ℝ) : Set (Fin n → ℤ) :=
  {z | (∀ i, (z i : ℝ) ∈ I i) ∧
    ∀ p, MvPolynomial.eval (fun i => (z i : ZMod p.val)) (P p) = 0}

/-- Exact agreement between the literal real-interval solution set and
the finite integer-endpoint representation. -/
theorem sourcePolynomialBoxSet_eq_integer {n : ℕ} (m : ℕ) (hm : m ≠ 0)
    (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) → MvPolynomial (Fin n) (ZMod p.val))
    (I : Fin n → Set ℝ) (a b : Fin n → ℤ)
    (hI : ∀ i (z : ℤ), (z : ℝ) ∈ I i ↔ a i ≤ z ∧ z ≤ b i) :
    sourcePolynomialBoxSet m P I =
      (polynomialBoxSolutions m.primeFactors (extendPolynomialBoxFamily m P) a b :
        Set (Fin n → ℤ)) := by
  ext z
  simp only [sourcePolynomialBoxSet, Set.mem_setOf_eq, Finset.mem_coe,
    mem_polynomialBoxSolutions, mem_integerPolynomialBox]
  constructor
  · rintro ⟨hz, hP⟩
    refine ⟨fun i => (hI i (z i)).mp (hz i), ?_⟩
    intro p hp
    have hpm := (Nat.mem_primeFactors_of_ne_zero hm).mp hp
    rw [extendPolynomialBoxFamily_apply m P ⟨p, hpm⟩]
    exact hP ⟨p, hpm⟩
  · rintro ⟨hz, hP⟩
    refine ⟨fun i => (hI i (z i)).mpr (hz i), ?_⟩
    intro p
    have hp := (Nat.mem_primeFactors_of_ne_zero hm).mpr p.property
    have he := hP p.val hp
    rw [extendPolynomialBoxFamily_apply m P p] at he
    exact he

/-- Complete Lemma 2.4. Each interval contains finitely many integers,
and its integer cardinality is at most the common real bound `Y`.
The polynomial data are supplied only at the primes dividing `m`.
The conclusion includes finiteness of the actual solution set and the
exact coefficient-uniform bound from the manuscript. -/
theorem source_polynomial_box (n E m : ℕ) (hn : 1 ≤ n) (hE : 1 ≤ E)
    (hm : 1 ≤ m) (hsq : Squarefree m)
    (P : (p : {p : ℕ // p.Prime ∧ p ∣ m}) → MvPolynomial (Fin n) (ZMod p.val))
    (hP : ∀ p, P p ≠ 0) (hdeg : ∀ p, (P p).totalDegree ≤ E)
    (I : Fin n → Set ℝ) (hI : ∀ i, (I i).OrdConnected)
    (hfin : ∀ i, ((fun z : ℤ => (z : ℝ)) ⁻¹' I i).Finite)
    (Y : ℝ) (hY : 1 ≤ Y)
    (hcard : ∀ i, (((hfin i).toFinset).card : ℝ) ≤ Y) :
    (sourcePolynomialBoxSet m P I).Finite ∧
      ((sourcePolynomialBoxSet m P I).ncard : ℝ) ≤
        ((∑ j ∈ Finset.Icc 1 n, E ^ j : ℕ) : ℝ) ^
          ArithmeticFunction.cardDistinctFactors m *
          (Y ^ n / (m : ℝ) + Y ^ (n - 1)) := by
  classical
  have hm0 : m ≠ 0 := by omega
  choose a b hab using fun i => realInterval_integer_membership_Icc (I i) (hI i) (hfin i)
  have hIeq (i : Fin n) : (hfin i).toFinset = Finset.Icc (a i) (b i) := by
    ext z
    simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_Icc] using hab i z
  have hPe : ∀ p ∈ m.primeFactors, extendPolynomialBoxFamily m P p ≠ 0 := by
    intro p hp
    have hpm := (Nat.mem_primeFactors_of_ne_zero hm0).mp hp
    rw [extendPolynomialBoxFamily_apply m P ⟨p, hpm⟩]
    exact hP ⟨p, hpm⟩
  have hdege : ∀ p ∈ m.primeFactors, (extendPolynomialBoxFamily m P p).totalDegree ≤ E := by
    intro p hp
    have hpm := (Nat.mem_primeFactors_of_ne_zero hm0).mp hp
    rw [extendPolynomialBoxFamily_apply m P ⟨p, hpm⟩]
    exact hdeg ⟨p, hpm⟩
  have hb := polynomialBox_squarefree_card_le n E m hn hE hm hsq
    (extendPolynomialBoxFamily m P) hPe hdege a b Y hY
    (fun i => by rw [← hIeq i]; exact hcard i)
  rw [sourcePolynomialBoxSet_eq_integer m hm0 P I a b hab]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  simpa only [polynomialBoxConstant_eq_sum_Icc,
    polynomialBox_primeFactors_card_eq_omega] using hb

end QuaternaryQuadraticForms
