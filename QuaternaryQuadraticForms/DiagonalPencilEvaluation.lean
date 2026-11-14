import QuaternaryQuadraticForms.DiagonalPencilAlgebra
import QuaternaryQuadraticForms.PrimeQuadraticGauss
import QuaternaryQuadraticForms.PrimeRamanujan

/-!
# Exact regular and singular diagonal pencil contributions

The raw pencil sum retains the factor `p τ_p` used in additive
orthogonality.  Each regular parameter contributes `p² τ_p χ_p(-Φ_u(t))`.
At a singular parameter the zero coefficient is treated separately, so
the Ramanujan value at zero and all four singular members remain present.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal contribution of one pencil parameter before division by
the orthogonality and Gauss factors. -/
def diagonalPencilRawSum (p : ℕ) [Fact p.Prime]
    (a b u : Fin 4 → ZMod p) (t : ZMod p) : ℂ :=
  ∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
    ∏ i : Fin 4, primeQuadraticExponentialSum p
      ((s : ZMod p) * diagonalPencilCoeff a b t i) (u i)

private theorem standardAddChar_prod {ι : Type*} (p : ℕ) [Fact p.Prime]
    (S : Finset ι) (f : ι → ZMod p) :
    (∏ i ∈ S, ZMod.stdAddChar (f i)) = ZMod.stdAddChar (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, AddChar.map_add_eq_mul]

private theorem quadraticExponentialSum_prod {ι : Type*}
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset ι) (c u : ι → ZMod p) (s : (ZMod p)ˣ)
    (hc : ∀ i ∈ S, c i ≠ 0) :
    (∏ i ∈ S, primeQuadraticExponentialSum p ((s : ZMod p) * c i) (u i)) =
      primeQuadraticGauss p ^ S.card *
        complexQuadraticChar p (s : ZMod p) ^ S.card *
        complexQuadraticChar p (∏ i ∈ S, c i) *
        ZMod.stdAddChar (-(∑ i ∈ S, u i ^ 2 / c i) / (4 * (s : ZMod p))) := by
  have hphase (i : ι) :
      -(u i ^ 2) / (4 * ((s : ZMod p) * c i)) =
        -(u i ^ 2 / c i) / (4 * (s : ZMod p)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hphase_sum :
      (∑ i ∈ S, -(u i ^ 2 / c i) / (4 * (s : ZMod p))) =
        -(∑ i ∈ S, u i ^ 2 / c i) / (4 * (s : ZMod p)) := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  calc
    _ = ∏ i ∈ S,
        (complexQuadraticChar p (s : ZMod p) * complexQuadraticChar p (c i) *
          primeQuadraticGauss p *
          ZMod.stdAddChar (-(u i ^ 2 / c i) / (4 * (s : ZMod p)))) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [primeQuadraticExponentialSum_of_ne_zero p hp _ _
        (mul_ne_zero s.ne_zero (hc i hi)), map_mul, hphase]
    _ = primeQuadraticGauss p ^ S.card *
        complexQuadraticChar p (s : ZMod p) ^ S.card *
        complexQuadraticChar p (∏ i ∈ S, c i) *
        ZMod.stdAddChar (-(∑ i ∈ S, u i ^ 2 / c i) / (4 * (s : ZMod p))) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const]
      rw [← map_prod (complexQuadraticChar p), standardAddChar_prod, hphase_sum]
      ring

private theorem quadraticChar_fourth (p : ℕ) [Fact p.Prime]
    (x : ZMod p) (hx : x ≠ 0) : complexQuadraticChar p x ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, complexQuadraticChar_sq_apply p x hx,
    one_pow]

private theorem four_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
  convert mul_ne_zero h2 h2 using 1
  norm_num

private theorem quadraticChar_mul_neg_div_four
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (d w : ZMod p) :
    complexQuadraticChar p d * complexQuadraticChar p (-w / 4) =
      complexQuadraticChar p (-(d * w)) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
  have harg : d * (-w / 4) = -(d * w) * ((2 : ZMod p)⁻¹) ^ 2 := by
    field_simp [h2, four_ne_zero p hp]
    ring
  rw [← map_mul, harg, map_mul, map_pow,
    complexQuadraticChar_sq_apply p _ (inv_ne_zero h2), mul_one]

private theorem quadraticGauss_regular_product_sum
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (c u : Fin 4 → ZMod p) (hc : ∀ i, c i ≠ 0) :
    (∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
      ∏ i : Fin 4, primeQuadraticExponentialSum p ((s : ZMod p) * c i) (u i)) =
      (p : ℂ) ^ 2 * primeQuadraticGauss p *
        complexQuadraticChar p (-((∏ i, c i) * (∑ i, u i ^ 2 / c i))) := by
  have hprod (s : (ZMod p)ˣ) :
      (∏ i : Fin 4, primeQuadraticExponentialSum p ((s : ZMod p) * c i) (u i)) =
        primeQuadraticGauss p ^ 4 * complexQuadraticChar p (∏ i, c i) *
          ZMod.stdAddChar (-(∑ i, u i ^ 2 / c i) / (4 * (s : ZMod p))) := by
    simpa only [Finset.card_univ, Fintype.card_fin, quadraticChar_fourth p _ s.ne_zero,
      mul_one] using quadraticExponentialSum_prod p hp Finset.univ c u s (fun i _ => hc i)
  calc
    _ = (primeQuadraticGauss p ^ 4 * complexQuadraticChar p (∏ i, c i)) *
        ∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
          ZMod.stdAddChar ((-(∑ i, u i ^ 2 / c i) / 4) / (s : ZMod p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [hprod, div_div]
      ring
    _ = (primeQuadraticGauss p ^ 4 * complexQuadraticChar p (∏ i, c i)) *
        (complexQuadraticChar p (-(∑ i, u i ^ 2 / c i) / 4) *
          primeQuadraticGauss p) := by
      rw [primeQuadraticGauss_units_div_inversion p hp]
    _ = (p : ℂ) ^ 2 * primeQuadraticGauss p *
        complexQuadraticChar p (-((∏ i, c i) * (∑ i, u i ^ 2 / c i))) := by
      rw [primeQuadraticGauss_fourth p hp]
      calc
        _ = (p : ℂ) ^ 2 * primeQuadraticGauss p *
          (complexQuadraticChar p (∏ i, c i) *
            complexQuadraticChar p (-(∑ i, u i ^ 2 / c i) / 4)) := by ring
        _ = _ := by rw [quadraticChar_mul_neg_div_four p hp]

private theorem quadraticGauss_singular_product_sum
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (c u : Fin 4 → ZMod p) (i : Fin 4) (hci : c i = 0)
    (hc : ∀ j, j ≠ i → c j ≠ 0) :
    (∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
      ∏ j : Fin 4, primeQuadraticExponentialSum p ((s : ZMod p) * c j) (u j)) =
      (p : ℂ) ^ 2 * primeQuadraticGauss p *
        (if u i = 0 then complexQuadraticChar p (-(∏ j ∈ Finset.univ.erase i, c j)) *
          primeRamanujan p (∑ j ∈ Finset.univ.erase i, u j ^ 2 / c j) else 0) := by
  classical
  by_cases hui : u i = 0
  · rw [if_pos hui]
    have hprod (s : (ZMod p)ˣ) :
        complexQuadraticChar p (s : ZMod p) *
          (∏ j : Fin 4, primeQuadraticExponentialSum p ((s : ZMod p) * c j) (u j)) =
        (p : ℂ) * primeQuadraticGauss p ^ 3 *
          complexQuadraticChar p (∏ j ∈ Finset.univ.erase i, c j) *
          ZMod.stdAddChar (-(∑ j ∈ Finset.univ.erase i, u j ^ 2 / c j) /
            (4 * (s : ZMod p))) := by
      rw [← Finset.prod_erase_mul Finset.univ
        (fun j : Fin 4 => primeQuadraticExponentialSum p ((s : ZMod p) * c j) (u j))
        (Finset.mem_univ i)]
      rw [hci, mul_zero, primeQuadraticExponentialSum_zero, if_pos hui,
        quadraticExponentialSum_prod p hp (Finset.univ.erase i) c u s
          (fun j hj => hc j (Finset.ne_of_mem_erase hj))]
      have hcard : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by simp
      rw [hcard]
      calc
        _ = (p : ℂ) * primeQuadraticGauss p ^ 3 *
            complexQuadraticChar p (∏ j ∈ Finset.univ.erase i, c j) *
            ZMod.stdAddChar (-(∑ j ∈ Finset.univ.erase i, u j ^ 2 / c j) /
              (4 * (s : ZMod p))) * complexQuadraticChar p (s : ZMod p) ^ 4 := by ring
        _ = _ := by rw [quadraticChar_fourth p _ s.ne_zero, mul_one]
    simp_rw [hprod]
    rw [← Finset.mul_sum, primeRamanujan_reciprocal_phase p (four_ne_zero p hp)]
    have hcube : primeQuadraticGauss p ^ 3 =
        primeQuadraticGauss p * (complexQuadraticChar p (-1) * (p : ℂ)) := by
      rw [pow_succ, primeQuadraticGauss_sq p hp]
      ring
    rw [hcube, show -(∏ j ∈ Finset.univ.erase i, c j) =
      (-1 : ZMod p) * (∏ j ∈ Finset.univ.erase i, c j) by ring, map_mul]
    ring
  · rw [if_neg hui, mul_zero]
    apply Finset.sum_eq_zero
    intro s _
    have hprod : (∏ j : Fin 4,
        primeQuadraticExponentialSum p ((s : ZMod p) * c j) (u j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hci, mul_zero, primeQuadraticExponentialSum_zero, if_neg hui]
    rw [hprod, mul_zero]

/-- The exact contribution of a regular pencil member, before division
by the orthogonality and Gauss factors. -/
theorem diagonalPencilRawSum_regular
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b u : Fin 4 → ZMod p) (t : ZMod p)
    (hc : ∀ i, diagonalPencilCoeff a b t i ≠ 0) :
    diagonalPencilRawSum p a b u t =
      (p : ℂ) ^ 2 * primeQuadraticGauss p *
        complexQuadraticChar p (-(diagonalPencilPhi a b u).eval t) := by
  have hphase :
      (∏ i, diagonalPencilCoeff a b t i) *
        (∑ i, u i ^ 2 / diagonalPencilCoeff a b t i) =
      (diagonalPencilPhi a b u).eval t := by
    change diagonalPencilDelta a b t * _ = _
    rw [← diagonalPencilPhi_div_delta a b u t hc, ← mul_div_assoc,
      mul_div_cancel_left₀ _ (diagonalPencilDelta_ne_zero a b t hc)]
  unfold diagonalPencilRawSum
  rw [quadraticGauss_regular_product_sum p hp _ u hc, hphase]

/-- The exact contribution of every singular pencil member.  The formula
keeps the full Ramanujan sum when `ν_i(u)` is zero. -/
theorem diagonalPencilRawSum_singular
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b u : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0)
    (i : Fin 4) :
    diagonalPencilRawSum p a b u (diagonalPencilRoot a b i) =
      (p : ℂ) ^ 2 * primeQuadraticGauss p *
        (if u i = 0 then complexQuadraticChar p (diagonalKappa a b i) *
          primeRamanujan p (diagonalPencilNu a b u i) else 0) := by
  have hpairi : ∀ j : Fin 4, j ≠ i → a i * b j - a j * b i ≠ 0 :=
    fun j hj => hpair i j hj.symm
  have hdelta : diagonalPencilDeltaAtRoot a b i ≠ 0 :=
    diagonalPencilDeltaAtRoot_ne_zero a b i (ha i) hpairi
  have hchar : complexQuadraticChar p (-diagonalPencilDeltaAtRoot a b i) =
      complexQuadraticChar p (diagonalKappa a b i) := by
    rw [neg_diagonalPencilDeltaAtRoot_eq a b i (ha i), div_eq_mul_inv, ← inv_pow,
      map_mul, map_pow, quadraticChar_fourth p _ (inv_ne_zero (ha i)), mul_one]
  have hram : primeRamanujan p (diagonalPencilW a b u i) =
      primeRamanujan p (diagonalPencilNu a b u i) := by
    rw [diagonalPencilW_eq a b u i (ha i) hpairi]
    calc
      _ = primeRamanujan p
          ((a i ^ 2 * diagonalPencilDeltaAtRoot a b i)⁻¹ *
            diagonalPencilNu a b u i) := by
        rw [div_eq_mul_inv, mul_comm]
      _ = _ := primeRamanujan_mul p _ _
        (inv_ne_zero (mul_ne_zero (pow_ne_zero 2 (ha i)) hdelta))
  have hraw := quadraticGauss_singular_product_sum p hp
    (diagonalPencilCoeff a b (diagonalPencilRoot a b i)) u i
    (diagonalPencilCoeff_at_own_root a b i (ha i))
    (fun j hj => diagonalPencilCoeff_at_root_ne_zero a b i j (ha i) (hpairi j hj))
  change diagonalPencilRawSum p a b u (diagonalPencilRoot a b i) =
    (p : ℂ) ^ 2 * primeQuadraticGauss p *
      (if u i = 0 then complexQuadraticChar p (-diagonalPencilDeltaAtRoot a b i) *
        primeRamanujan p (diagonalPencilW a b u i) else 0) at hraw
  rw [hraw, hchar, hram]

end QuaternaryQuadraticForms
