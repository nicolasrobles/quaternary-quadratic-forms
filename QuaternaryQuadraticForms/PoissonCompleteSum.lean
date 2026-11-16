import QuaternaryQuadraticForms.PoissonResidueSummation

/-!
# The actual complete sums in the Poisson expansion

The finite arithmetic Fourier coefficient is exactly the manuscript's
mixed complete sum, with its original prime-product weight, congruence
condition, unit parameter, and positive frequency phase.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Adding the positive Fourier phase converts the zero-frequency arithmetic
summand into the literal mixed summand at frequency u. -/
theorem mixedIntegerSummand_fourier_phase
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u x : Fin 4 → ℤ) (a : ℤ) :
    mixedIntegerSummand ξ q c A 0 a x *
      ZMod.stdAddChar ((dotProduct u x : ℤ) : ZMod (q * c)) =
        mixedIntegerSummand ξ q c A u a x := by
  unfold mixedIntegerSummand
  by_cases hx : (q : ℤ) ∣ integralQuadraticValue A x
  · simp only [if_pos hx, zero_dotProduct, add_zero, Int.cast_add,
      AddChar.map_add_eq_mul]
    ring
  · simp only [if_neg hx, zero_mul]

/-- The Fourier coefficient after summing over all unit parameters is the
existing literal mixed complete sum, including q=1 and c=1. -/
theorem poisson_mixed_fourier_coefficient
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    (∑ a : (ZMod c)ˣ, poissonResidueFourierSum (q * c)
      (fun x => mixedIntegerSummand ξ q c A 0 ((a : ZMod c).val : ℤ) x) u) =
        mixedCompleteSum ξ q c A u := by
  unfold poissonResidueFourierSum mixedCompleteSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro z _
  exact mixedIntegerSummand_fourier_phase ξ q c A u (residueLift (q * c) z) _

/-- Poisson summation of the actual periodic arithmetic factors gives the
literal mixed complete sum, and the frequency series is absolutely convergent. -/
theorem poisson_mixed_complete_sum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (g : RealVector4 → ℂ) (f : (Fin 4 → ℤ) → ℂ)
    (hg : (Function.support (fun x : Fin 4 → ℤ => g (integerRealVector x))).Finite)
    (hf : Summable (fun u => ‖f u‖))
    (hpoisson : ∀ z : Fin 4 → ℤ,
      (∑' m : Fin 4 → ℤ,
        g (integerRealVector z + ((q * c : ℕ) : ℝ) • integerRealVector m)) =
          (((q * c : ℕ) : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
            ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod (q * c)) * f u) :
    ((∑ a : (ZMod c)ˣ, ∑' x : Fin 4 → ℤ,
      mixedIntegerSummand ξ q c A 0 ((a : ZMod c).val : ℤ) x *
        g (integerRealVector x)) =
      (((q * c : ℕ) : ℂ) ^ 4)⁻¹ *
        ∑' u : Fin 4 → ℤ, mixedCompleteSum ξ q c A u * f u) ∧
      Summable (fun u : Fin 4 → ℤ => ‖mixedCompleteSum ξ q c A u * f u‖) := by
  classical
  let b (a : (ZMod c)ˣ) (x : Fin 4 → ℤ) :=
    mixedIntegerSummand ξ q c A 0 ((a : ZMod c).val : ℤ) x
  have hp : ∀ z : Fin 4 → ℤ,
      (∑' m : Fin 4 → ℤ,
        g (integerRealVector (fun i => z i + ((q * c : ℕ) : ℤ) * m i))) =
          (((q * c : ℕ) : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
            ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod (q * c)) * f u := by
    intro z
    have he (m : Fin 4 → ℤ) :
        integerRealVector (fun i => z i + ((q * c : ℕ) : ℤ) * m i) =
          integerRealVector z + ((q * c : ℕ) : ℝ) • integerRealVector m := by
      ext i
      simp [integerRealVector]
    simpa only [he] using hpoisson z
  have hcoeff (u : Fin 4 → ℤ) :
      (∑ a : (ZMod c)ˣ, poissonResidueFourierSum (q * c) (b a) u) =
        mixedCompleteSum ξ q c A u :=
    poisson_mixed_fourier_coefficient ξ q c A u
  have hs (a : (ZMod c)ˣ) :
      Summable (fun u => poissonResidueFourierSum (q * c) (b a) u * f u) :=
    (poisson_residue_fourier_summable (q * c) (b a) f hf).of_norm
  have hsall : Summable (fun u : Fin 4 → ℤ => mixedCompleteSum ξ q c A u * f u) := by
    have hh : Summable (fun u : Fin 4 → ℤ =>
        ∑ a : (ZMod c)ˣ, poissonResidueFourierSum (q * c) (b a) u * f u) :=
      summable_sum (fun a _ => hs a)
    simpa only [← Finset.sum_mul, hcoeff] using hh
  refine ⟨?_, hsall.norm⟩
  calc
    _ = ∑ a : (ZMod c)ˣ, (((q * c : ℕ) : ℂ) ^ 4)⁻¹ *
        ∑' u : Fin 4 → ℤ, poissonResidueFourierSum (q * c) (b a) u * f u := by
      apply Finset.sum_congr rfl
      intro a _
      apply poisson_periodic_weight (q * c) (b a)
        (fun x => g (integerRealVector x)) f _ hg hf hp
      intro x y hxy
      exact mixedIntegerSummand_x_congr ξ q c A 0 _ x y hxy
    _ = (((q * c : ℕ) : ℂ) ^ 4)⁻¹ *
        ∑' u : Fin 4 → ℤ, ∑ a : (ZMod c)ˣ,
          poissonResidueFourierSum (q * c) (b a) u * f u := by
      rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun a _ => hs a)]
    _ = _ := by simp only [← Finset.sum_mul, hcoeff]

end QuaternaryQuadraticForms
