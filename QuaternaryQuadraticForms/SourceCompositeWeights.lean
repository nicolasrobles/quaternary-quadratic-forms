import QuaternaryQuadraticForms.SourceWeights

/-!
# Composite weights of the original supplied source family

This is the literal product over prime divisors of a modulus coprime to
`N`. Each factor uses the original supplied function. Its equality with
the total-family representation used in the complete sums is proved.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The manuscript's composite weight, using only the supplied functions
at primes outside `N`. -/
def sourceCompositeWeight (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (hqN : q.Coprime N) (x : Fin 4 → ℤ) : ℂ :=
  ∏ p : q.primeFactors,
    ξ p.val (Nat.prime_of_mem_primeFactors p.property)
      ((Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
        (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)))
      (fun i => (x i : ZMod p.val))

/-- The representation inside the actual complete sums agrees with the
literal product of the original source functions. -/
theorem compositeWeight_extend_eq_source (N q : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hqN : q.Coprime N) (x : Fin 4 → ℤ) :
    compositeWeight (extendPrimeWeights N ξ) q x =
      sourceCompositeWeight N ξ q hqN x :=
  compositeWeight_extend N q ξ hqN x

end QuaternaryQuadraticForms
