import QuaternaryQuadraticForms.SharedSupportCompleteSum

/-!
# The complete mixed sum at every good modulus

The literal source factors are `gcd(q,c)` and its quotient in `q`.
Squarefreeness makes the quotient coprime to the shared block. The
actual CRT identity separates its constrained Fourier sum, and the
proved shared-support evaluation supplies all remaining factors.
-/

noncomputable section

namespace QuaternaryQuadraticForms

local instance (q c : ℕ) [NeZero q] : NeZero (q.gcd c) :=
  ⟨Nat.gcd_ne_zero_left (NeZero.ne q)⟩

local instance (q c : ℕ) [NeZero q] : NeZero (q / q.gcd c) :=
  ⟨(Nat.div_gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

private theorem restrict_prime_weight_invariance
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q d : ℕ) [NeZero q] (hξ : PrimeWeightsInvariant ξ q) (hd : d ∣ q) :
    PrimeWeightsInvariant ξ d := by
  intro p hp r hr x
  exact hξ p (Nat.primeFactors_mono hd (NeZero.ne q) hp) r hr x

/-- Lemma 3.5's good-modulus identity, with the actual gcd and quotient,
the existing complete sums, and the actual Jacobi character value. -/
theorem mixedCompleteSum_good_modulus
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ q c A u =
      constrainedFourierSum ξ (q / q.gcd c) A u *
        (q.gcd c : ℂ) * (c : ℂ) ^ 2 *
          globalQuadraticChar A.det (q.gcd c * c) *
            compositeWeight ξ (q.gcd c) (A.adjugate.mulVec u) *
              integralRamanujanSum (q.gcd c * c)
                (dotProduct u (A.adjugate.mulVec u)) := by
  obtain ⟨hprod, _, _, hd, _, hcop, hdc⟩ :=
    squarefree_gcd_factors q c hq (NeZero.ne c)
  have heq : q / q.gcd c * q.gcd c = q := by
    simpa only [Nat.mul_comm] using hprod
  have hξprod : PrimeWeightsInvariant ξ (q / q.gcd c * q.gcd c) := by
    simpa only [heq] using hξ
  have hsplit := mixedCompleteSum_crt ξ (q / q.gcd c) (q.gcd c) 1 c A u
    (by simpa only [Nat.mul_one] using hcop) hξprod
  have hξd := restrict_prime_weight_invariance ξ q (q.gcd c) hξ (Nat.gcd_dvd_left q c)
  have hsplit' : mixedCompleteSum ξ q c A u =
      constrainedFourierSum ξ (q / q.gcd c) A u * mixedCompleteSum ξ (q.gcd c) c A u := by
    simpa only [heq, Nat.one_mul, mixedCompleteSum_one_right] using hsplit
  rw [hsplit', mixedCompleteSum_shared_support ξ (q.gcd c) c hd hdc A hA hc hξd u]
  ring

end QuaternaryQuadraticForms
