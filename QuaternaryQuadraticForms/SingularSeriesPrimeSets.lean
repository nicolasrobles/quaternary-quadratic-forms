import Mathlib.Data.Nat.Factorization.Defs

/-!
# Finite sets of prime divisors for singular-series corrections

The factors are indexed by the actual prime subtype, so the finite products
fit the same index type as the infinite Euler products.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The finite set of prime divisors of a natural number, indexed as primes. -/
def singularSeriesPrimeDivisors (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.subtype Nat.Prime

/-- For a nonzero integer, membership is exactly divisibility by the prime. -/
theorem mem_singularSeriesPrimeDivisors (n : ℕ) (hn : n ≠ 0) (p : Nat.Primes) :
    p ∈ singularSeriesPrimeDivisors n ↔ (p : ℕ) ∣ n := by
  rw [singularSeriesPrimeDivisors, Finset.mem_subtype]
  exact ⟨fun h => (Nat.mem_primeFactors.mp h).2.1,
    fun h => Nat.mem_primeFactors.mpr ⟨p.property, h, hn⟩⟩

end QuaternaryQuadraticForms
