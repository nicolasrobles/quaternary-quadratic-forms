import QuaternaryQuadraticForms.GlobalQuadraticCharacter
import QuaternaryQuadraticForms.UnramifiedCompleteSum
import QuaternaryQuadraticForms.CompleteSumFactorization
import QuaternaryQuadraticForms.RamanujanMultiplicativity

/-!
# The unweighted complete sum at every good positive modulus

Prime-power induction combines the already proved actual Gauss evaluation
with the actual CRT identity and Ramanujan multiplicativity. The coefficient
is the Jacobi symbol, whose agreement with the original source Dirichlet
character is proved in `GlobalQuadraticCharacter`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The exact unweighted formula at every positive modulus coprime to the
source's `N_F`, including modulus one and every integral frequency. -/
theorem unweightedCompleteSum_good_modulus
    (c : ℕ) [NeZero c] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hcgood : c.Coprime (quadraticBadPrimeModulus A))
    (u : Fin 4 → ℤ) :
    unweightedCompleteSum c A u =
      globalQuadraticChar A.det c * (c : ℂ) ^ 2 *
        integralRamanujanSum c (dotProduct u (A.adjugate.mulVec u)) := by
  have hall : ∀ (n : ℕ) (hn : n ≠ 0), n.Coprime (quadraticBadPrimeModulus A) →
      @unweightedCompleteSum n ⟨hn⟩ A u =
        globalQuadraticChar A.det n * (n : ℂ) ^ 2 *
          @integralRamanujanSum n ⟨hn⟩ (dotProduct u (A.adjugate.mulVec u)) := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p k hp hk hn hgood
      letI : Fact p.Prime := ⟨hp⟩
      have hpgood : ¬ p ∣ quadraticBadPrimeModulus A :=
        hp.coprime_iff_not_dvd.mp
          ((Nat.coprime_pow_left_iff hk p (quadraticBadPrimeModulus A)).mp hgood)
      simpa only [globalQuadraticChar_prime_power, Nat.cast_pow, ← pow_mul,
        Nat.mul_comm k 2] using
        unweightedCompleteSum_prime_power p k hk A hA hpgood u
    · intro hn
      exact (hn rfl).elim
    · intro _ _
      rw [unweightedCompleteSum_one, globalQuadraticChar_one,
        integralRamanujanSum_modulus_one]
      norm_num
    · intro a b _ _ hab iha ihb hab0 hgood
      letI : NeZero a := ⟨left_ne_zero_of_mul hab0⟩
      letI : NeZero b := ⟨right_ne_zero_of_mul hab0⟩
      have hparts := Nat.coprime_mul_iff_left.mp hgood
      rw [unweightedCompleteSum_mul a b A u hab,
        iha (NeZero.ne a) hparts.1, ihb (NeZero.ne b) hparts.2,
        globalQuadraticChar_mul,
        integralRamanujanSum_mul a b hab (dotProduct u (A.adjugate.mulVec u)),
        Nat.cast_mul, mul_pow]
      ring
  exact hall c (NeZero.ne c) hcgood

end QuaternaryQuadraticForms
