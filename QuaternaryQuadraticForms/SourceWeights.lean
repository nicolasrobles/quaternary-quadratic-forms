import QuaternaryQuadraticForms.CompleteSums

/-!
# Local weight families defined only at the source's good primes

The source gives `ξ_p` only for prime `p` not dividing `N`. Extending by
zero elsewhere is harmless: for `(q,N)=1`, every factor in `ξ_q` uses
one of the original supplied functions. No property at excluded primes
is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Extend the source family only to make a total index type available. -/
def extendPrimeWeights (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) (x : Fin 4 → ZMod p) : ℂ :=
  if hp : p.Prime then if hN : ¬p ∣ N then ξ p hp hN x else 0 else 0

/-- At every supplied prime, extension agrees with the original function. -/
theorem extendPrimeWeights_apply (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) (hp : p.Prime) (hN : ¬p ∣ N) (x : Fin 4 → ZMod p) :
    extendPrimeWeights N ξ p x = ξ p hp hN x := by
  simp only [extendPrimeWeights, dif_pos hp, dif_pos hN]

/-- The source invariance at good primes supplies exactly the invariance
needed at the primes of a modulus coprime to `N`. -/
theorem primeWeightsInvariant_extend (N q : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hqN : q.Coprime N)
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y) :
    PrimeWeightsInvariant (extendPrimeWeights N ξ) q := by
  intro p hp r hr y
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hN : ¬p ∣ N := hprime.coprime_iff_not_dvd.mp
    (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  simpa only [extendPrimeWeights_apply N ξ p hprime hN] using hξ p hprime hN r hr y

/-- The extended family's composite weight is exactly the product of the
original supplied local functions; no excluded-prime value enters it. -/
theorem compositeWeight_extend (N q : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hqN : q.Coprime N) (x : Fin 4 → ℤ) :
    compositeWeight (extendPrimeWeights N ξ) q x =
      ∏ p : q.primeFactors,
        ξ p.val (Nat.prime_of_mem_primeFactors p.property)
          ((Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
            (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)))
          (fun i => (x i : ZMod p.val)) := by
  unfold compositeWeight
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  exact extendPrimeWeights_apply N ξ p.val (Nat.prime_of_mem_primeFactors p.property)
    ((Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
      (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property))) _

end QuaternaryQuadraticForms
