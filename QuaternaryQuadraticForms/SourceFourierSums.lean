import QuaternaryQuadraticForms.SourceCompositeWeights
import QuaternaryQuadraticForms.CompleteSumFactorization

/-!
# Fourier sums of the original supplied source functions

The sum below uses the literal product of the functions supplied at primes
outside `N`. Its equality with the existing constrained Fourier sum is
proved. The source prime-factor identity then follows from the checked CRT
theorem, including the empty product at modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The manuscript's `C_q(u)`, with the original good-prime function family. -/
def sourceConstrainedFourierSum (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ x : Fin 4 → ZMod q,
    if (q : ℤ) ∣ integralQuadraticValue A (residueLift q x) then
      sourceCompositeWeight N ξ q hqN (residueLift q x) *
        ZMod.stdAddChar ((dotProduct u (residueLift q x) : ℤ) : ZMod q)
    else 0

/-- The internal complete sum is exactly the original source sum. -/
theorem constrainedFourierSum_extend_eq_source (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    constrainedFourierSum (extendPrimeWeights N ξ) q A u =
      sourceConstrainedFourierSum N ξ q hqN A u := by
  simp only [constrainedFourierSum, sourceConstrainedFourierSum,
    compositeWeight_extend_eq_source N q ξ hqN]

/-- At a good prime this is the actual finite-field Fourier transform of
the supplied function on the quadratic cone. -/
theorem sourceConstrainedFourierSum_prime (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p ∣ N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    sourceConstrainedFourierSum N ξ p
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN) A u =
      ∑ x ∈ Finset.univ.filter (fun x : PrimeVector p =>
          quadraticValue (A.map (Int.castRingHom (ZMod p))) x = 0),
        ξ p Fact.out hpN x * ZMod.stdAddChar (dotProduct (reduceFrequency p u) x) := by
  rw [← constrainedFourierSum_extend_eq_source, constrainedFourierSum_prime]
  simp only [extendPrimeWeights_apply N ξ p Fact.out hpN]

/-- The source's empty-prime-product convention gives `C_1(u)=1`. -/
theorem sourceConstrainedFourierSum_one (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hN : Nat.Coprime 1 N) (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    sourceConstrainedFourierSum N ξ 1 hN A u = 1 := by
  rw [← constrainedFourierSum_extend_eq_source, constrainedFourierSum_one]

/-- The exact source prime-factor identity, with no values required at
excluded primes and no restriction on the frequency. -/
theorem sourceConstrainedFourierSum_primeFactors (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hsq : Squarefree q)
    (hξ : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y) :
    sourceConstrainedFourierSum N ξ q hqN A u =
      ∏ p : q.primeFactors,
        @sourceConstrainedFourierSum N ξ p.val
          ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
          (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)) A u := by
  rw [← constrainedFourierSum_extend_eq_source,
    constrainedFourierSum_primeFactors (extendPrimeWeights N ξ) q A u hsq
      (primeWeightsInvariant_extend N q ξ hqN hξ)]
  apply Finset.prod_congr rfl
  intro p _
  letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  exact constrainedFourierSum_extend_eq_source N ξ p.val
    (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)) A u

end QuaternaryQuadraticForms
