import QuaternaryQuadraticForms.DiagonalForms
import QuaternaryQuadraticForms.DiagonalGeometry
import QuaternaryQuadraticForms.GeometricReduction

/-!
# Diagonal smoothness and the exact prime reduction criterion

The field-level diagonal rank calculation is applied to the actual integral
equations after mapping to the relevant algebraic closure. In characteristic
zero, the source's six nonzero pair determinants imply smoothness. At every
prime outside `N_F`, the actual geometric good-reduction condition fails
exactly when that prime divides the source product `M`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Over an algebraically closed field of odd characteristic, the actual
diagonal rank condition is equivalent to nonvanishing of the six-factor
pair product, when all coefficients of the first form are nonzero. -/
theorem diagonal_projectiveIntersectionTransverseRank_iff_pairProduct_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (a b : Fin 4 → K)
    (h2 : (2 : K) ≠ 0) (ha : ∀ i, a i ≠ 0) :
    ProjectiveIntersectionTransverseRank
        (matrixQuadraticPolynomial (Matrix.diagonal a))
        (matrixQuadraticPolynomial (Matrix.diagonal b)) ↔
      diagonalPairProduct a b ≠ 0 := by
  rw [diagonal_projectiveIntersectionTransverseRank_iff a b h2 ha,
    diagonalPairProduct_ne_zero_iff]
  exact ⟨fun h i j hij => h i j hij.ne,
    fun h i j hij => diagonal_pair_difference_ne_zero a b h i j hij⟩

/-- The actual diagonal pair satisfies the manuscript's characteristic-zero
smoothness condition under its nonsingularity and six-determinant hypotheses. -/
theorem diagonal_smooth_characteristicZero (a b : Fin 4 → ℤ)
    (hα : (∏ i, a i) ≠ 0)
    (hΔlt : ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0) :
    SmoothCharacteristicZero (Matrix.diagonal a)
      (matrixQuadraticPolynomial (Matrix.diagonal b)) := by
  unfold SmoothCharacteristicZero
  rw [diagonalQuadraticPolynomial_map, diagonalQuadraticPolynomial_map]
  apply diagonal_projectiveIntersectionTransverseRank
  · norm_num
  · intro i
    change (a i : AlgebraicClosure ℚ) ≠ 0
    exact_mod_cast diagonal_coefficients_ne_zero a hα i
  · intro i j hij
    change (a i : AlgebraicClosure ℚ) * (b j : AlgebraicClosure ℚ) -
      (a j : AlgebraicClosure ℚ) * (b i : AlgebraicClosure ℚ) ≠ 0
    exact_mod_cast diagonal_pair_difference_ne_zero a b hΔlt i j hij

/-- At a prime outside the actual quadratic bad-prime modulus, the literal
geometric reduction of the diagonal pair is bad exactly when the prime
divides the six-factor product `M`. The integral pair determinants need not
be nonzero for this equivalence, and coefficients of the second form may vanish. -/
theorem diagonal_badReductionAt_iff (p : ℕ) [Fact p.Prime]
    (a b : Fin 4 → ℤ)
    (hpF : ¬ p ∣ quadraticBadPrimeModulus (Matrix.diagonal a)) :
    ¬ GoodReductionAt p (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) ↔
      (p : ℤ) ∣ diagonalPairProduct a b := by
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let g : ZMod p →+* AlgebraicClosure (ZMod p) := algebraMap _ _
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro hz
    exact hpF (dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff 2 p).mp hz) _)
  have h2 : (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro hz
    apply h2p
    apply g.injective
    simpa only [map_ofNat, map_zero] using hz
  have ha : ∀ i, f (a i) ≠ 0 := by
    have hdet := goodPrime_reduced_det_ne_zero p (Matrix.diagonal a) hpF
    change ((Matrix.diagonal a).map f).det ≠ 0 at hdet
    apply diagonal_coefficients_ne_zero (f ∘ a)
    intro hz
    apply hdet
    exact (f.map_det (Matrix.diagonal a)).symm.trans (by
      simpa only [Matrix.det_diagonal, map_prod, Function.comp_apply] using hz)
  have haK : ∀ i, (g ∘ (f ∘ a)) i ≠ 0 := by
    intro i hz
    apply ha i
    apply g.injective
    simpa only [Function.comp_apply, map_zero] using hz
  have hzero : g (f (diagonalPairProduct a b)) = 0 ↔
      f (diagonalPairProduct a b) = 0 := by
    constructor
    · intro hz
      apply g.injective
      simpa only [map_zero] using hz
    · intro hz
      rw [hz, map_zero]
  have hgood : GoodReductionAt p (Matrix.diagonal a)
      (matrixQuadraticPolynomial (Matrix.diagonal b)) ↔
        ¬ (p : ℤ) ∣ diagonalPairProduct a b := by
    unfold GoodReductionAt
    change ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial ((Matrix.diagonal a).map f)).map g)
      (((matrixQuadraticPolynomial (Matrix.diagonal b)).map f).map g) ↔ _
    rw [← matrixQuadraticPolynomial_map_ring f (Matrix.diagonal a)]
    simp only [diagonalQuadraticPolynomial_map]
    rw [diagonal_projectiveIntersectionTransverseRank_iff_pairProduct_ne_zero
      _ _ h2 haK, diagonalPairProduct_map g, diagonalPairProduct_map f]
    exact not_congr (hzero.trans
      (ZMod.intCast_zmod_eq_zero_iff_dvd (diagonalPairProduct a b) p))
  simpa only [not_not] using not_congr hgood

end QuaternaryQuadraticForms
