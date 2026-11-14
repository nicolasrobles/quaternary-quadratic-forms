import QuaternaryQuadraticForms.CompleteSumCRT
import QuaternaryQuadraticForms.CompleteSumInvariance
import QuaternaryQuadraticForms.SourceWeights

/-!
# Complete Lemma 3.1

Both assertions concern the actual mixed complete sum. The final source
wrapper accepts local functions only at primes not dividing `N`. Their
extension is proved to agree with every factor occurring when `(q,N)=1`.
The argument works without the source's additional squarefreeness,
weight-size, or nondegeneracy hypotheses.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Both assertions of Lemma 3.1 for the literal mixed sums and their actual
prime-product weights. -/
theorem complete_sum_crt
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : PrimeWeightsInvariant ξ (q₁ * q₂)) :
    (mixedCompleteSum ξ (q₁ * q₂) (c₁ * c₂) A u =
      mixedCompleteSum ξ q₁ c₁ A u * mixedCompleteSum ξ q₂ c₂ A u) ∧
    (∀ t : ℤ, t.gcd (((q₁ * q₂) * (c₁ * c₂) : ℕ) : ℤ) = 1 →
      mixedCompleteSum ξ (q₁ * q₂) (c₁ * c₂) A (fun i => t * u i) =
        mixedCompleteSum ξ (q₁ * q₂) (c₁ * c₂) A u) :=
  ⟨mixedCompleteSum_crt ξ q₁ q₂ c₁ c₂ A u hcoprime hξ,
    fun t ht => mixedCompleteSum_unit_frequency ξ (q₁ * q₂) (c₁ * c₂) A u t hξ ht⟩

/-- Source-domain CRT multiplicativity: only local functions at primes
not dividing `N` are supplied or assumed invariant. -/
theorem source_mixedCompleteSum_crt (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hqN : (q₁ * q₂).Coprime N)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y) :
    mixedCompleteSum (extendPrimeWeights N ξ) (q₁ * q₂) (c₁ * c₂) A u =
      mixedCompleteSum (extendPrimeWeights N ξ) q₁ c₁ A u *
        mixedCompleteSum (extendPrimeWeights N ξ) q₂ c₂ A u :=
  mixedCompleteSum_crt (extendPrimeWeights N ξ) q₁ q₂ c₁ c₂ A u hcoprime
    (primeWeightsInvariant_extend N (q₁ * q₂) ξ hqN hξ)

/-- Source-domain unit-frequency invariance for every integer scalar with
the manuscript's exact gcd condition, including modulus one. -/
theorem source_mixedCompleteSum_unit_frequency (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (t : ℤ)
    (hqN : q.Coprime N)
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
    (ht : t.gcd ((q * c : ℕ) : ℤ) = 1) :
    mixedCompleteSum (extendPrimeWeights N ξ) q c A (fun i => t * u i) =
      mixedCompleteSum (extendPrimeWeights N ξ) q c A u :=
  mixedCompleteSum_unit_frequency (extendPrimeWeights N ξ) q c A u t
    (primeWeightsInvariant_extend N q ξ hqN hξ) ht

/-- Every clause of Lemma 3.1 for precisely the source's supplied prime
functions and integral quadratic form and frequency. -/
theorem source_complete_sum_crt (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hqN : (q₁ * q₂).Coprime N)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y) :
    (mixedCompleteSum (extendPrimeWeights N ξ) (q₁ * q₂) (c₁ * c₂) A u =
      mixedCompleteSum (extendPrimeWeights N ξ) q₁ c₁ A u *
        mixedCompleteSum (extendPrimeWeights N ξ) q₂ c₂ A u) ∧
    (∀ t : ℤ, t.gcd (((q₁ * q₂) * (c₁ * c₂) : ℕ) : ℤ) = 1 →
      mixedCompleteSum (extendPrimeWeights N ξ) (q₁ * q₂) (c₁ * c₂) A
          (fun i => t * u i) =
        mixedCompleteSum (extendPrimeWeights N ξ) (q₁ * q₂) (c₁ * c₂) A u) :=
  complete_sum_crt (extendPrimeWeights N ξ) q₁ q₂ c₁ c₂ A u hcoprime
    (primeWeightsInvariant_extend N (q₁ * q₂) ξ hqN hξ)

end QuaternaryQuadraticForms
