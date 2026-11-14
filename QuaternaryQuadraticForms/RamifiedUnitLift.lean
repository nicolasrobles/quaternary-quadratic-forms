import QuaternaryQuadraticForms.PrimePowerUnitDigits
import QuaternaryQuadraticForms.WeightedGaussSums
import QuaternaryQuadraticForms.CRTCharacters

/-!
# The scalar unit-digit bridge for the ramified mixed sum

Splitting the actual units modulo `p*c` into `a+c*t` leaves one scalar
character sum modulo `p`. Its orthogonality imposes exactly the cone
condition in the mixed complete sum and contributes a factor `p`.
The argument needs no condition on the matrix, frequency, or local weight.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem sum_stdAddChar_val_mul
    (p : ℕ) [NeZero p] (z : ℤ) :
    (∑ t : ZMod p, ZMod.stdAddChar (((t.val : ℤ) * z : ℤ) : ZMod p)) =
      if (p : ℤ) ∣ z then (p : ℂ) else 0 := by
  classical
  simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ZMod.card, apply_ite, Nat.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] using
    AddChar.sum_mulShift (z : ZMod p) (ZMod.isPrimitive_stdAddChar p)

private theorem unit_digit_phase (p c : ℕ) [NeZero p] [NeZero c]
    (a t q l : ℤ) :
    ZMod.stdAddChar (((a + (c : ℤ) * t) * q + l : ℤ) : ZMod (p * c)) =
      ZMod.stdAddChar ((a * q + l : ℤ) : ZMod (p * c)) *
        ZMod.stdAddChar ((t * q : ℤ) : ZMod p) := by
  rw [show (a + (c : ℤ) * t) * q + l =
    (a * q + l) + (c : ℤ) * (t * q) by ring]
  rw [Int.cast_add, AddChar.map_add_eq_mul, stdAddChar_mul_modulus]

private theorem sum_weighted_unit_digit (p c : ℕ) [NeZero p] [NeZero c]
    (w : ℂ) (a q l : ℤ) :
    (∑ t : ZMod p,
      w * ZMod.stdAddChar
        (((a + (c : ℤ) * (t.val : ℤ)) * q + l : ℤ) : ZMod (p * c))) =
      (p : ℂ) * (if (p : ℤ) ∣ q then
        w * ZMod.stdAddChar ((a * q + l : ℤ) : ZMod (p * c)) else 0) := by
  classical
  simp_rw [unit_digit_phase, ← mul_assoc]
  rw [← Finset.mul_sum, sum_stdAddChar_val_mul]
  split_ifs <;> ring

/-- The literal weighted unit sum at modulus `p*c` is `p` times the mixed
complete sum whenever `p` is prime and divides the positive modulus `c`.
The matrix, frequency, and whole family of local weights are arbitrary. -/
theorem primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum
    (p c : ℕ) [Fact p.Prime] [NeZero c] (hpc : p ∣ c)
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    primeWeightedCompleteSum p (p * c) (ξ p) A u =
      (p : ℂ) * mixedCompleteSum ξ p c A u := by
  classical
  unfold primeWeightedCompleteSum
  rw [sum_units_residueLift_digits c p hpc
    (fun a => weightedIntegralGaussSum p (p * c) (ξ p) A a u)]
  simp only [weightedIntegralGaussSum]
  unfold mixedCompleteSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_weighted_unit_digit]
  congr 1
  unfold mixedIntegerSummand
  rw [compositeWeight_prime ξ p (Fact.out : p.Prime)]

/-- The exact source bridge `𝒰_(k+1) = p * 𝒮_(p,p^k)` for every `k ≥ 1`.
There is no symmetry, nonsingularity, weight-invariance, or parity premise. -/
theorem primeWeightedCompleteSum_prime_power_lift
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    primeWeightedCompleteSum p (p ^ (k + 1)) (ξ p) A u =
      (p : ℂ) * mixedCompleteSum ξ p (p ^ k) A u := by
  simpa only [pow_succ, Nat.mul_comm (p ^ k) p] using
    primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum p (p ^ k)
      (dvd_pow_self p (by omega)) ξ A u

end QuaternaryQuadraticForms
