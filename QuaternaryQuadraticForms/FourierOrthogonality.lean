import QuaternaryQuadraticForms.DiagonalGeometry
import QuaternaryQuadraticForms.FiniteCharacters

/-!
# Additive orthogonality for the actual quadratic-cone Fourier sum

The cone constraint is expanded using the standard prime-field additive
character. The diagonal exponential sum then separates into its four
one-dimensional factors, with the positive Fourier phase of the source.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Orthogonality of the actual standard additive character. -/
theorem stdAddChar_orthogonality (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ v : ZMod p, ZMod.stdAddChar (v * c)) =
      if c = 0 then (p : ℂ) else 0 := by
  simpa only [ZMod.card, apply_ite, Nat.cast_zero] using
    AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar p)

/-- The cone condition in the literal Fourier sum is an additive-character
average. This identity does not require nonsingularity or smoothness. -/
theorem fourierSum_additive_expansion (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p))
    (u : PrimeVector p) :
    (p : ℂ) * fourierSum A ψ G u =
      ∑ v : ZMod p, ∑ x : PrimeVector p,
        polynomialCharacterWeight ψ G x *
          ZMod.stdAddChar (v * quadraticValue A x + dotProduct u x) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [AddChar.map_add_eq_mul]
  have hinner (x : PrimeVector p) :
      (∑ v : ZMod p, polynomialCharacterWeight ψ G x *
          (ZMod.stdAddChar (v * quadraticValue A x) *
            ZMod.stdAddChar (dotProduct u x))) =
        if quadraticValue A x = 0 then
          (p : ℂ) * (polynomialCharacterWeight ψ G x *
            ZMod.stdAddChar (dotProduct u x)) else 0 := by
    calc
      _ = (polynomialCharacterWeight ψ G x *
            ZMod.stdAddChar (dotProduct u x)) *
          ∑ v : ZMod p, ZMod.stdAddChar (v * quadraticValue A x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [stdAddChar_orthogonality]
        split_ifs <;> ring
  simp_rw [hinner]
  simp only [fourierSum, Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- An additive character carries a finite sum to the product of its values. -/
theorem stdAddChar_sum {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, ih]

/-- The actual four-variable diagonal exponential sum factors into the
one-dimensional quadratic sums used in the pencil calculation. -/
theorem diagonal_exponential_sum_factorization (p : ℕ) [Fact p.Prime]
    (a b u : Fin 4 → ZMod p) (s t : ZMod p) :
    (∑ x : PrimeVector p,
      ZMod.stdAddChar
        (s * MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal b)) +
          (s * t) * quadraticValue (Matrix.diagonal a) x + dotProduct u x)) =
      ∏ i : Fin 4, ∑ y : ZMod p,
        ZMod.stdAddChar (s * (b i + t * a i) * y ^ 2 + u i * y) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hquad : quadraticValue (Matrix.diagonal a) x = ∑ i, a i * x i ^ 2 := by
    rw [← eval_matrixQuadraticPolynomial_quadraticValue]
    exact eval_diagonalQuadraticPolynomial a x
  rw [eval_diagonalQuadraticPolynomial, hquad]
  have hphase :
      s * (∑ i, b i * x i ^ 2) + (s * t) * (∑ i, a i * x i ^ 2) +
          dotProduct u x =
        ∑ i, (s * (b i + t * a i) * x i ^ 2 + u i * x i) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hphase]
  exact stdAddChar_sum p Finset.univ _

end QuaternaryQuadraticForms
