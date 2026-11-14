import QuaternaryQuadraticForms.GaussNorm
import QuaternaryQuadraticForms.IntegerMatrixKernelBound
import QuaternaryQuadraticForms.DoubledMatrixKernel
import QuaternaryQuadraticForms.GaussBoundConstants

/-!
# Uniform inner Gauss bounds for the actual integral form

The squared-norm identity selects the kernel of `2 • A` modulo the actual
modulus. Its cardinality is bounded by the absolute integer determinant,
which is sixteen times that of the source quaternary matrix. This works at
all positive moduli, without a good-prime or modular nonsingularity condition.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The squared norm of every actual unit-parameter Gauss sum has the source
bound, including at moduli divisible by bad primes. -/
theorem quadraticGaussSum_integral_norm_sq_le (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (a : (ZMod n)ˣ) (u : Fin 4 → ZMod n) :
    ‖quadraticGaussSum n (reduceQuadraticMatrix n A) (a : ZMod n) u‖ ^ 2 ≤
      (n : ℝ) ^ 4 * (16 * (A.det.natAbs : ℝ)) := by
  have htwo : ((2 : ℤ) • A).det ≠ 0 := by
    rw [quaternary_det_two_smul]
    exact mul_ne_zero (by norm_num) hdet
  have hkernel := matrixResidueKernel_card_le_det n ((2 : ℤ) • A) htwo
  rw [quaternary_det_two_smul_natAbs] at hkernel
  have hkernel_real : ((matrixResidueKernel n ((2 : ℤ) • A)).card : ℝ) ≤
      16 * (A.det.natAbs : ℝ) := by exact_mod_cast hkernel
  have hnorm := quadraticGaussSum_norm_sq_le_kernel_card n
    (reduceQuadraticMatrix n A) (reduceQuadraticMatrix_symmetric n A hA) a u
  rw [← matrixResidueKernel_two_smul] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left hkernel_real (by positivity))

/-- The actual inner Gauss sum has norm at most `4 sqrt(|det A|) n²`
for every unit scalar and every residue frequency. -/
theorem quadraticGaussSum_integral_norm_le (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (a : (ZMod n)ˣ) (u : Fin 4 → ZMod n) :
    ‖quadraticGaussSum n (reduceQuadraticMatrix n A) (a : ZMod n) u‖ ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) * (n : ℝ) ^ 2 :=
  gauss_norm_le_of_sq_le _ n _ (Nat.cast_nonneg _)
    (quadraticGaussSum_integral_norm_sq_le n A hA hdet a u)

/-- The same inner estimate for the literal integer data whenever the scalar
is a unit modulo the modulus, as required in the manuscript's proof. -/
theorem integralQuadraticGaussSum_norm_le (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (a : ℤ) (ha : IsUnit (a : ZMod n)) (u : Fin 4 → ℤ) :
    ‖integralQuadraticGaussSum n A a u‖ ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) * (n : ℝ) ^ 2 := by
  obtain ⟨v, hv⟩ := ha
  change ‖quadraticGaussSum n (reduceQuadraticMatrix n A) (a : ZMod n)
    (fun i => (u i : ZMod n))‖ ≤ _
  rw [← hv]
  exact quadraticGaussSum_integral_norm_le n A hA hdet v _

end QuaternaryQuadraticForms
