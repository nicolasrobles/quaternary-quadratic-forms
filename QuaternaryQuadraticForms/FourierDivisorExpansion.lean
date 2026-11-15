import QuaternaryQuadraticForms.CongruenceBoxDefinitions
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Expansion of the exceptional-prime factors

The finite product in equation (3.32) is expanded over the actual
divisors of the squarefree modulus. The indicator at a divisor is the
original product of the supplied polynomial zero indicators, including
the empty product at modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Divisors of a squarefree modulus correspond to subsets of its prime
divisors, with the empty subset corresponding to one. -/
theorem squarefree_divisor_sum_eq_powerset {R : Type*} [AddCommMonoid R]
    (q : ℕ) (hsq : Squarefree q) (f : ℕ → R) :
    (∑ h ∈ q.divisors, f h) =
      ∑ s ∈ q.primeFactors.powerset, f (∏ p ∈ s, p) := by
  classical
  symm
  apply Finset.sum_bij (fun s _ => ∏ p ∈ s, p)
  · intro s hs
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hsq.ne_zero⟩
    have hd := Finset.prod_dvd_prod_of_subset s q.primeFactors (fun p => p)
      (Finset.mem_powerset.mp hs)
    simpa only [Nat.prod_primeFactors_of_squarefree hsq] using hd
  · intro s hs t ht hst
    have hsprime : ∀ p ∈ s, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hs) hp)
    have htprime : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp ht) hp)
    have hh := congrArg Nat.primeFactors hst
    simpa only [Nat.primeFactors_prod hsprime, Nat.primeFactors_prod htprime] using hh
  · intro h hh
    have hd := Nat.dvd_of_mem_divisors hh
    refine ⟨h.primeFactors, Finset.mem_powerset.mpr
      (Nat.primeFactors_mono hd hsq.ne_zero), ?_⟩
    exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hd)
  · intro s _
    rfl

/-- The literal exceptional-prime product is the divisor expansion in
equation (3.32), without a positivity or nonvanishing premise on `D`. -/
theorem exceptional_prime_product_eq_divisor_sum
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q : ℕ) (hsq : Squarefree q) (u : Fin 4 → ℤ) :
    (∏ p ∈ q.primeFactors,
      (1 + (p : ℝ) ^ (1 / 2 : ℝ) *
        (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p) = 0 then 1 else 0))) =
      ∑ h ∈ q.divisors, (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u := by
  classical
  rw [Finset.prod_one_add, squarefree_divisor_sum_eq_powerset q hsq]
  apply Finset.sum_congr rfl
  intro s hs
  have hsprime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hs) hp)
  rw [Finset.prod_mul_distrib,
    Real.finset_prod_rpow s (fun p => (p : ℝ)) (fun p _ => Nat.cast_nonneg p),
    exceptionalIndicator, Nat.primeFactors_prod hsprime, Nat.cast_prod]

end QuaternaryQuadraticForms
