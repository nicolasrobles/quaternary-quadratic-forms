import QuaternaryQuadraticForms.FourierGaussExpansion
import QuaternaryQuadraticForms.DiagonalPencilEvaluation

/-!
# The exact diagonal pencil formula

The finite set below consists of the actual singular parameters. Splitting
the full pencil sum at this set retains each of its four singular members.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The set of singular parameters of the diagonal pencil. -/
def diagonalPencilRoots {K : Type*} [Field K] [DecidableEq K]
    (a b : Fin 4 → K) : Finset K := Finset.univ.image (diagonalPencilRoot a b)

/-- Membership names one of the four actual singular parameters. -/
theorem mem_diagonalPencilRoots {K : Type*} [Field K] [DecidableEq K]
    (a b : Fin 4 → K) (t : K) :
    t ∈ diagonalPencilRoots a b ↔ ∃ i, diagonalPencilRoot a b i = t := by
  classical
  simp only [diagonalPencilRoots, Finset.mem_image, Finset.mem_univ, true_and]

/-- There are at most four excluded parameters, even before distinctness
has been deduced from the pair determinants. -/
theorem diagonalPencilRoots_card_le {K : Type*} [Field K] [DecidableEq K]
    (a b : Fin 4 → K) :
    (diagonalPencilRoots a b).card ≤ 4 := by
  classical
  simpa only [diagonalPencilRoots, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_image_le (s := Finset.univ) (f := diagonalPencilRoot a b))

/-- The sum over all parameters splits into regular parameters and the
four singular members once their parameters are distinct. -/
theorem diagonalPencil_sum_split {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (a b : Fin 4 → K) (hinj : Function.Injective (diagonalPencilRoot a b))
    (f : K → ℂ) :
    (∑ t : K, f t) = (∑ t ∈ Finset.univ \ diagonalPencilRoots a b, f t) +
      ∑ i : Fin 4, f (diagonalPencilRoot a b i) := by
  classical
  have himage : (∑ t ∈ diagonalPencilRoots a b, f t) =
      ∑ i : Fin 4, f (diagonalPencilRoot a b i) := by
    unfold diagonalPencilRoots
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact hinj hij
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ (diagonalPencilRoots a b)), himage]
  ring

/-- The exact Fourier pencil identity, including all four singular
members and their full prime Ramanujan factors. -/
theorem diagonal_fourier_pencil_formula (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (a b u : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0) :
    fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u =
      (p : ℂ) * (∑ t ∈ Finset.univ \ diagonalPencilRoots a b,
        complexQuadraticChar p (-(diagonalPencilPhi a b u).eval t)) +
      (p : ℂ) * (∑ i ∈ Finset.univ.filter (fun i => u i = 0),
        complexQuadraticChar p (diagonalKappa a b i) *
          primeRamanujan p (diagonalPencilNu a b u i)) := by
  classical
  have hregular :
      (∑ t ∈ Finset.univ \ diagonalPencilRoots a b,
        diagonalPencilRawSum p a b u t) =
      ((p : ℂ) ^ 2 * primeQuadraticGauss p) *
        ∑ t ∈ Finset.univ \ diagonalPencilRoots a b,
          complexQuadraticChar p (-(diagonalPencilPhi a b u).eval t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply diagonalPencilRawSum_regular p hp a b u t
    intro i hi
    apply (Finset.mem_sdiff.mp ht).2
    apply (mem_diagonalPencilRoots a b t).mpr
    exact ⟨i, ((diagonalPencilCoeff_eq_zero_iff a b t i (ha i)).mp hi).symm⟩
  have hsingular :
      (∑ i : Fin 4, diagonalPencilRawSum p a b u (diagonalPencilRoot a b i)) =
      ((p : ℂ) ^ 2 * primeQuadraticGauss p) *
        ∑ i ∈ Finset.univ.filter (fun i => u i = 0),
          complexQuadraticChar p (diagonalKappa a b i) *
            primeRamanujan p (diagonalPencilNu a b u i) := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact diagonalPencilRawSum_singular p hp a b u ha hpair i
  have hraw := diagonal_fourier_pencil_expansion p hp a b u
  change (p : ℂ) * primeQuadraticGauss p *
      fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u =
    ∑ t : ZMod p, diagonalPencilRawSum p a b u t at hraw
  rw [diagonalPencil_sum_split a b (diagonalPencilRoot_injective a b ha hpair),
    hregular, hsingular] at hraw
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero hpC (primeQuadraticGauss_ne_zero p hp))
  calc
    _ = ((p : ℂ) ^ 2 * primeQuadraticGauss p) *
        (∑ t ∈ Finset.univ \ diagonalPencilRoots a b,
          complexQuadraticChar p (-(diagonalPencilPhi a b u).eval t)) +
      ((p : ℂ) ^ 2 * primeQuadraticGauss p) *
        (∑ i ∈ Finset.univ.filter (fun i => u i = 0),
          complexQuadraticChar p (diagonalKappa a b i) *
            primeRamanujan p (diagonalPencilNu a b u i)) := hraw
    _ = _ := by ring

end QuaternaryQuadraticForms
