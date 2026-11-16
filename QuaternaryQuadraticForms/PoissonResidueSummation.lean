import QuaternaryQuadraticForms.PoissonResidueClasses

/-!
# Poisson summation with a periodic arithmetic weight

The analytic Poisson identity is an explicit hypothesis here. The result
performs only exact residue decomposition and justified sum interchanges.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The finite Fourier sum of a periodic lattice weight on residue representatives. -/
def poissonResidueFourierSum (n : ℕ) [NeZero n]
    (b : (Fin 4 → ℤ) → ℂ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ z : Fin 4 → ZMod n, b (residueLift n z) *
    ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n)

/-- A finite arithmetic Fourier sum preserves absolute summability of the analytic factor. -/
theorem poisson_residue_fourier_summable (n : ℕ) [NeZero n]
    (b : (Fin 4 → ℤ) → ℂ) (f : (Fin 4 → ℤ) → ℂ)
    (hf : Summable (fun u => ‖f u‖)) :
    Summable (fun u => ‖poissonResidueFourierSum n b u * f u‖) := by
  have hs : Summable (fun u : Fin 4 → ℤ =>
      ∑ z : Fin 4 → ZMod n, b (residueLift n z) *
        (ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n) * f u)) := by
    apply summable_sum
    intro z _
    exact Summable.mul_left _ (poisson_phase_mul_summable n (residueLift n z) f hf)
  have hs' : Summable (fun u => poissonResidueFourierSum n b u * f u) := by
    simpa only [poissonResidueFourierSum, Finset.sum_mul, mul_assoc] using hs
  exact hs'.norm

/-- The exact weighted Poisson identity for any periodic lattice weight.
The spatial sum is finite and the frequency sum is absolutely convergent. -/
theorem poisson_periodic_weight (n : ℕ) [NeZero n]
    (b G f : (Fin 4 → ℤ) → ℂ)
    (hb : ∀ x y : Fin 4 → ℤ,
      (∀ i, (x i : ZMod n) = (y i : ZMod n)) → b x = b y)
    (hG : (Function.support G).Finite)
    (hf : Summable (fun u => ‖f u‖))
    (hpoisson : ∀ z : Fin 4 → ℤ,
      (∑' m : Fin 4 → ℤ, G (fun i => z i + (n : ℤ) * m i)) =
        ((n : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
          ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod n) * f u) :
    (∑' x : Fin 4 → ℤ, b x * G x) =
      ((n : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ, poissonResidueFourierSum n b u * f u := by
  classical
  have hfinite : (Function.support (fun x => b x * G x)).Finite := by
    apply hG.subset
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hzero
    exact hx (by rw [hzero, mul_zero])
  have hper (z : Fin 4 → ZMod n) (m : Fin 4 → ℤ) :
      b (poissonResidueVector n z m) = b (residueLift n z) := by
    apply hb
    intro i
    rw [poissonResidueVector_cast, residueLift_cast]
  have hfreq (z : Fin 4 → ZMod n) :
      Summable (fun u : Fin 4 → ℤ => b (residueLift n z) *
        (ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n) * f u)) :=
    Summable.mul_left _ (poisson_phase_mul_summable n (residueLift n z) f hf)
  calc
    _ = ∑ z : Fin 4 → ZMod n, ∑' m : Fin 4 → ℤ,
        b (poissonResidueVector n z m) * G (poissonResidueVector n z m) :=
      poisson_tsum_residue_classes n _ hfinite
    _ = ∑ z : Fin 4 → ZMod n, b (residueLift n z) *
        (∑' m : Fin 4 → ℤ, G (poissonResidueVector n z m)) := by
      simp_rw [hper, tsum_mul_left]
    _ = ∑ z : Fin 4 → ZMod n, b (residueLift n z) *
        (((n : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
          ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n) * f u) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [show (∑' m : Fin 4 → ℤ, G (poissonResidueVector n z m)) = _ from
        hpoisson (residueLift n z)]
    _ = ((n : ℂ) ^ 4)⁻¹ * ∑ z : Fin 4 → ZMod n,
        ∑' u : Fin 4 → ℤ, b (residueLift n z) *
          (ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n) * f u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [tsum_mul_left]
      ring
    _ = ((n : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
        ∑ z : Fin 4 → ZMod n, b (residueLift n z) *
          (ZMod.stdAddChar ((dotProduct u (residueLift n z) : ℤ) : ZMod n) * f u) := by
      rw [Summable.tsum_finsetSum (fun z _ => hfreq z)]
    _ = _ := by
      simp only [poissonResidueFourierSum, Finset.sum_mul, mul_assoc]

end QuaternaryQuadraticForms
