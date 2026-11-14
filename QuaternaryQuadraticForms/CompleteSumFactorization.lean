import QuaternaryQuadraticForms.CompleteSumCRT
import QuaternaryQuadraticForms.CompleteSumSpecializations
import Mathlib.Data.Nat.Squarefree

/-!
# Prime factorization of the literal local sums

These are the immediate source corollaries of the mixed CRT identity.
The empty prime product at modulus one is included. Local scalar
invariance is required only at the primes dividing the specified modulus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem primeWeightsInvariant_of_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d : ℕ) [NeZero q] (hξ : PrimeWeightsInvariant ξ q) (hd : d ∣ q) :
    PrimeWeightsInvariant ξ d := by
  intro p hp r hr x
  exact hξ p (Nat.primeFactors_mono hd (NeZero.ne q) hp) r hr x

private theorem map_squarefree_prime_product {R : Type*} [CommMonoid R]
    (f : ℕ → R) (q : ℕ) (hsq : Squarefree q) (hone : f 1 = 1)
    (hmul : ∀ a b : ℕ, a ∣ q → b ∣ q → a.Coprime b →
      f (a * b) = f a * f b) :
    f q = ∏ p ∈ q.primeFactors, f p := by
  have hprod (s : Finset ℕ) : s ⊆ q.primeFactors →
      f (∏ p ∈ s, p) = ∏ p ∈ s, f p := by
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa using hone
    | @insert p s hps ih =>
        intro hs
        have hp : p ∈ q.primeFactors := hs (Finset.mem_insert_self p s)
        have hs' : s ⊆ q.primeFactors := fun k hk => hs (Finset.mem_insert_of_mem hk)
        have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
        have hsdvd : (∏ k ∈ s, k) ∣ q :=
          (Finset.prod_dvd_prod_of_subset s q.primeFactors (fun k => k) hs').trans
            (Nat.prod_primeFactors_dvd q)
        have hcoprime : p.Coprime (∏ k ∈ s, k) := by
          apply Nat.Coprime.prod_right
          intro k hk
          apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors (hs' hk))).mpr
          exact fun hpk => hps (hpk.symm ▸ hk)
        rw [Finset.prod_insert hps, Finset.prod_insert hps,
          hmul p _ hpdvd hsdvd hcoprime, ih hs']
  simpa only [Nat.prod_primeFactors_of_squarefree hsq] using
    hprod q.primeFactors Finset.Subset.rfl

private theorem constrained_prime_product_of_mul
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hsq : Squarefree q) (hξ : PrimeWeightsInvariant ξ q)
    (hone : constrainedFourierSum ξ 1 A u = 1)
    (hmul : ∀ (a b : ℕ) [NeZero a] [NeZero b], a.Coprime b →
      PrimeWeightsInvariant ξ (a * b) →
      constrainedFourierSum ξ (a * b) A u =
        constrainedFourierSum ξ a A u * constrainedFourierSum ξ b A u) :
    constrainedFourierSum ξ q A u =
      ∏ p : q.primeFactors,
        @constrainedFourierSum ξ p.1 ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩ A u := by
  classical
  let f : ℕ → ℂ := fun k =>
    if hk : k = 0 then 0 else @constrainedFourierSum ξ k ⟨hk⟩ A u
  have hf1 : f 1 = 1 := by
    simpa only [f, dif_neg (by decide : (1 : ℕ) ≠ 0)] using hone
  have hfmul (a b : ℕ) (ha : a ∣ q) (hb : b ∣ q) (hab : a.Coprime b) :
      f (a * b) = f a * f b := by
    letI : NeZero a := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne q) ha⟩
    letI : NeZero b := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne q) hb⟩
    have hξab := primeWeightsInvariant_of_dvd ξ q (a * b) hξ
      (hab.mul_dvd_of_dvd_of_dvd ha hb)
    simpa only [f, dif_neg (NeZero.ne (a * b)), dif_neg (NeZero.ne a),
      dif_neg (NeZero.ne b)] using hmul a b hab hξab
  calc
    constrainedFourierSum ξ q A u = f q := by
      simp only [f, dif_neg (NeZero.ne q)]
    _ = ∏ p ∈ q.primeFactors, f p :=
      map_squarefree_prime_product f q hsq hf1 hfmul
    _ = ∏ p : q.primeFactors,
        @constrainedFourierSum ξ p.1 ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩ A u := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro p _
      simp only [f, dif_neg (Nat.prime_of_mem_primeFactors p.2).ne_zero]

/-- The source's unweighted complete sum is multiplicative in coprime
positive moduli, including a factor equal to one. -/
theorem unweightedCompleteSum_mul (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hcoprime : c₁.Coprime c₂) :
    unweightedCompleteSum (c₁ * c₂) A u =
      unweightedCompleteSum c₁ A u * unweightedCompleteSum c₂ A u := by
  let ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ := fun _ _ => 1
  have hξ : PrimeWeightsInvariant ξ (1 * 1) := by
    intro p hp
    simp at hp
  have h := mixedCompleteSum_crt ξ 1 1 c₁ c₂ A u
    (by simpa only [one_mul] using hcoprime) hξ
  simpa only [one_mul, mixedCompleteSum_one_left] using h

/-- The actual constrained Fourier sum is multiplicative in coprime
positive moduli under the source's local scalar invariance. -/
theorem constrainedFourierSum_mul
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hcoprime : q₁.Coprime q₂) (hξ : PrimeWeightsInvariant ξ (q₁ * q₂)) :
    constrainedFourierSum ξ (q₁ * q₂) A u =
      constrainedFourierSum ξ q₁ A u * constrainedFourierSum ξ q₂ A u := by
  have h := mixedCompleteSum_crt ξ q₁ q₂ 1 1 A u
    (by simpa only [mul_one] using hcoprime) hξ
  simpa only [mul_one, mixedCompleteSum_one_right] using h

/-- For a positive squarefree modulus, the actual constrained sum is the
product of its prime sums. The subtype indexes exactly the prime divisors
and supplies their positivity; at modulus one it is the empty product. -/
theorem constrainedFourierSum_primeFactors
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hsq : Squarefree q) (hξ : PrimeWeightsInvariant ξ q) :
    constrainedFourierSum ξ q A u =
      ∏ p : q.primeFactors,
        @constrainedFourierSum ξ p.1 ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩ A u := by
  apply constrained_prime_product_of_mul ξ q A u hsq hξ
  · exact constrainedFourierSum_one ξ A u
  · intro a b _ _ hab hξab
    exact constrainedFourierSum_mul ξ a b A u hab hξab

end QuaternaryQuadraticForms
