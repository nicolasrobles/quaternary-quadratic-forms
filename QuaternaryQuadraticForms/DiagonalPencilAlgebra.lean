import QuaternaryQuadraticForms.DiagonalPencil

/-!
# Regular and singular diagonal-pencil algebra

All identities use the literal coefficients, pair differences and source
forms. Nonvanishing hypotheses are only on the first coefficients and the
pair differences; individual second coefficients may vanish.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The vanishing parameter of the `i`th pencil coefficient is `-b_i/a_i`. -/
theorem diagonalPencilCoeff_eq_zero_iff {K : Type*} [Field K]
    (a b : Fin 4 → K) (t : K) (i : Fin 4) (ha : a i ≠ 0) :
    diagonalPencilCoeff a b t i = 0 ↔ t = diagonalPencilRoot a b i := by
  unfold diagonalPencilCoeff diagonalPencilRoot
  rw [eq_div_iff ha]
  constructor
  · intro h
    calc
      t * a i = (b i + t * a i) - b i := by ring
      _ = -b i := by rw [h]; ring
  · intro h
    rw [h]
    ring

/-- The indicated coefficient vanishes at its own singular parameter. -/
theorem diagonalPencilCoeff_at_own_root {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0) :
    diagonalPencilCoeff a b (diagonalPencilRoot a b i) i = 0 :=
  (diagonalPencilCoeff_eq_zero_iff a b _ i ha).mpr rfl

/-- Evaluation at another coefficient's root gives the literal pair
difference divided by its first coefficient. -/
theorem diagonalPencilCoeff_at_root {K : Type*} [Field K]
    (a b : Fin 4 → K) (i j : Fin 4) (ha : a i ≠ 0) :
    diagonalPencilCoeff a b (diagonalPencilRoot a b i) j =
      (a i * b j - a j * b i) / a i := by
  unfold diagonalPencilCoeff diagonalPencilRoot
  field_simp
  ring

/-- Distinct pair ratios make all three remaining coefficients nonzero. -/
theorem diagonalPencilCoeff_at_root_ne_zero {K : Type*} [Field K]
    (a b : Fin 4 → K) (i j : Fin 4) (ha : a i ≠ 0)
    (hpair : a i * b j - a j * b i ≠ 0) :
    diagonalPencilCoeff a b (diagonalPencilRoot a b i) j ≠ 0 := by
  rw [diagonalPencilCoeff_at_root a b i j ha]
  exact div_ne_zero hpair ha

/-- The four actual singular parameters are distinct. -/
theorem diagonalPencilRoot_injective {K : Type*} [Field K]
    (a b : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0) :
    Function.Injective (diagonalPencilRoot a b) := by
  intro i j hij
  by_contra hne
  have hn := diagonalPencilCoeff_at_root_ne_zero a b i j (ha i) (hpair i j hne)
  rw [hij, diagonalPencilCoeff_at_own_root a b j (ha j)] at hn
  exact hn rfl

/-- A prime field containing the four distinct singular parameters has
at least five elements. -/
theorem five_le_of_diagonalPencil_roots (p : ℕ) [Fact p.Prime]
    (a b : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0) :
    5 ≤ p := by
  have hc := Fintype.card_le_of_injective (diagonalPencilRoot a b)
    (diagonalPencilRoot_injective a b ha hpair)
  have hfour : 4 ≤ p := by simpa using hc
  have hp : p ≠ 4 := by
    intro h
    have hprime : Nat.Prime 4 := h ▸ Fact.out (p := p.Prime)
    exact (by decide : ¬ Nat.Prime 4) hprime
  omega

/-- Away from the four roots, the full coefficient product is nonzero. -/
theorem diagonalPencilDelta_ne_zero {K : Type*} [Field K]
    (a b : Fin 4 → K) (t : K)
    (hc : ∀ i, diagonalPencilCoeff a b t i ≠ 0) :
    diagonalPencilDelta a b t ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hc i

/-- The product of the three surviving coefficients is nonzero. -/
theorem diagonalPencilDeltaAtRoot_ne_zero {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0)
    (hpair : ∀ j : Fin 4, j ≠ i → a i * b j - a j * b i ≠ 0) :
    diagonalPencilDeltaAtRoot a b i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact diagonalPencilCoeff_at_root_ne_zero a b i j ha
    (hpair j (Finset.mem_erase.mp hj).1)

private theorem complement_sum_div_prod {ι K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) (c w : ι → K) (hc : ∀ i ∈ s, c i ≠ 0) :
    (∑ i ∈ s, w i * ∏ j ∈ s.erase i, c j) / (∏ i ∈ s, c i) =
      ∑ i ∈ s, w i / c i := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hprod : (∏ j ∈ s.erase i, c j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hc j (Finset.mem_of_mem_erase hj)
  rw [← Finset.mul_prod_erase s c hi]
  field_simp

/-- The regular pencil phase is the source numerator divided by the
actual product of the four coefficients. -/
theorem diagonalPencilPhi_div_delta {K : Type*} [Field K]
    (a b u : Fin 4 → K) (t : K)
    (hc : ∀ i, diagonalPencilCoeff a b t i ≠ 0) :
    (diagonalPencilPhi a b u).eval t / diagonalPencilDelta a b t =
      ∑ i, u i ^ 2 / diagonalPencilCoeff a b t i := by
  rw [eval_diagonalPencilPhi]
  exact complement_sum_div_prod Finset.univ (diagonalPencilCoeff a b t)
    (fun i => u i ^ 2) (fun i _ => hc i)

/-- The surviving product is the three pair differences divided by `a_i³`. -/
theorem diagonalPencilDeltaAtRoot_eq {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0) :
    diagonalPencilDeltaAtRoot a b i =
      (∏ j ∈ Finset.univ.erase i, (a i * b j - a j * b i)) / a i ^ 3 := by
  simp only [diagonalPencilDeltaAtRoot, diagonalPencilCoeff_at_root a b i _ ha]
  rw [Finset.prod_div_distrib]
  simp

/-- The sign and fourth-power factor in the source singular Gauss term. -/
theorem neg_diagonalPencilDeltaAtRoot_eq {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0) :
    -diagonalPencilDeltaAtRoot a b i = diagonalKappa a b i / a i ^ 4 := by
  rw [diagonalPencilDeltaAtRoot_eq a b i ha]
  unfold diagonalKappa
  field_simp
  ring_nf
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  ring

/-- The source singular coefficient is nonzero under the same literal
pair-difference assumptions. -/
theorem diagonalKappa_ne_zero {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0)
    (hpair : ∀ j : Fin 4, j ≠ i → a i * b j - a j * b i ≠ 0) :
    diagonalKappa a b i ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr ha)
  exact Finset.prod_ne_zero_iff.mpr fun j hj => hpair j (Finset.mem_erase.mp hj).1

/-- The singular reciprocal phase equals the actual source form `ν_i`
divided by its explicit nonzero scalar denominator. -/
theorem diagonalPencilW_eq {K : Type*} [Field K]
    (a b u : Fin 4 → K) (i : Fin 4) (ha : a i ≠ 0)
    (hpair : ∀ j : Fin 4, j ≠ i → a i * b j - a j * b i ≠ 0) :
    diagonalPencilW a b u i =
      diagonalPencilNu a b u i / (a i ^ 2 * diagonalPencilDeltaAtRoot a b i) := by
  have hc : ∀ j ∈ Finset.univ.erase i,
      diagonalPencilCoeff a b (diagonalPencilRoot a b i) j ≠ 0 := by
    intro j hj
    exact diagonalPencilCoeff_at_root_ne_zero a b i j ha
      (hpair j (Finset.mem_erase.mp hj).1)
  have hnum :
      (∑ j ∈ Finset.univ.erase i, u j ^ 2 *
        ∏ l ∈ (Finset.univ.erase i).erase j,
          diagonalPencilCoeff a b (diagonalPencilRoot a b i) l) =
      diagonalPencilNu a b u i / a i ^ 2 := by
    unfold diagonalPencilNu
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hcard : ((Finset.univ.erase i).erase j).card = 2 := by
      rw [Finset.card_erase_of_mem hj]
      simp
    simp only [diagonalPencilCoeff_at_root a b i _ ha, Finset.prod_div_distrib,
      Finset.prod_const, hcard]
    ring
  unfold diagonalPencilW
  rw [← complement_sum_div_prod (Finset.univ.erase i)
    (diagonalPencilCoeff a b (diagonalPencilRoot a b i)) (fun j => u j ^ 2) hc]
  rw [hnum, div_div]
  rfl

end QuaternaryQuadraticForms
