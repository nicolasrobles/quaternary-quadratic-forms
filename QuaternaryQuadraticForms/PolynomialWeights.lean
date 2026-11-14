import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial character weights

The weight in quadratic_character_sums_github.tex, Section 4, is the literal function
`x ↦ ψ (MvPolynomial.eval x G)`.  This file proves its three properties in
equation (3.1), `eq:weightproperties`.  The nonprincipal condition used in
Lemma 4.4 is unnecessary for these properties: mathlib extends every
multiplicative character, including the principal character, by zero at zero.

The scaling formula is proved from the monomials of the polynomial, rather
than included as a hypothesis on its evaluation function.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Evaluation of a homogeneous polynomial under scalar multiplication. -/
theorem homogeneous_eval_smul {σ R : Type*} [CommSemiring R]
    {G : MvPolynomial σ R} {n : ℕ} (hG : G.IsHomogeneous n)
    (t : R) (x : σ → R) :
    MvPolynomial.eval (t • x) G = t ^ n * MvPolynomial.eval x G := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hddegree : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hG (MvPolynomial.mem_support_iff.mp hd)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  change G.coeff d * (t ^ d.degree * _) = t ^ n * (G.coeff d * _)
  rw [hddegree]
  ac_rfl

/-- A homogeneous polynomial of positive degree vanishes at the zero vector. -/
theorem homogeneous_eval_zero {σ R : Type*} [CommSemiring R]
    {G : MvPolynomial σ R} {n : ℕ} (hG : G.IsHomogeneous n) (hn : n ≠ 0) :
    MvPolynomial.eval (0 : σ → R) G = 0 := by
  simpa [hn] using homogeneous_eval_smul hG (0 : R) (0 : σ → R)

/-- Coefficient reduction preserves the degree of homogeneity of the integer
polynomial in the manuscript. No good-reduction hypothesis is needed here. -/
theorem homogeneous_reduce_mod {σ : Type*} {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (p : ℕ) :
    (MvPolynomial.map (Int.castRingHom (ZMod p)) G).IsHomogeneous n :=
  hG.map (Int.castRingHom (ZMod p))

/-- The polynomial character weight used in Section 4 of the manuscript. -/
def polynomialCharacterWeight {σ K : Type*} [CommSemiring K]
    (ψ : MulChar K ℂ) (G : MvPolynomial σ K) (x : σ → K) : ℂ :=
  ψ (MvPolynomial.eval x G)

/-- The character weight vanishes at the zero vector. -/
theorem polynomialCharacterWeight_zero {σ K : Type*} [Field K]
    (ψ : MulChar K ℂ) {G : MvPolynomial σ K} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : n ≠ 0) :
    polynomialCharacterWeight ψ G (0 : σ → K) = 0 := by
  rw [polynomialCharacterWeight, homogeneous_eval_zero hG hn, ψ.map_zero]

/-- If `ψ ^ n` is principal, the weight is constant on each projective ray. -/
theorem polynomialCharacterWeight_units_smul {σ K : Type*} [Field K]
    (ψ : MulChar K ℂ) {G : MvPolynomial σ K} {n : ℕ}
    (hG : G.IsHomogeneous n) (hψ : ψ ^ n = 1)
    (t : Kˣ) (x : σ → K) :
    polynomialCharacterWeight ψ G (t • x) = polynomialCharacterWeight ψ G x := by
  change ψ (MvPolynomial.eval ((t : K) • x) G) = ψ (MvPolynomial.eval x G)
  rw [homogeneous_eval_smul hG, map_mul, map_pow]
  have ht : ψ (t : K) ^ n = 1 := by
    rw [← ψ.pow_apply_coe n t, hψ, MulChar.one_apply_coe]
  rw [ht, one_mul]

/-- Scalar invariance in the manuscript's nonzero-scalar formulation. -/
theorem polynomialCharacterWeight_smul {σ K : Type*} [Field K]
    (ψ : MulChar K ℂ) {G : MvPolynomial σ K} {n : ℕ}
    (hG : G.IsHomogeneous n) (hψ : ψ ^ n = 1)
    {t : K} (ht : t ≠ 0) (x : σ → K) :
    polynomialCharacterWeight ψ G (t • x) = polynomialCharacterWeight ψ G x :=
  polynomialCharacterWeight_units_smul ψ hG hψ (Units.mk0 t ht) x

/-- Every polynomial character weight over `ZMod p` has norm at most one. -/
theorem polynomialCharacterWeight_norm_le_one {σ : Type*} {p : ℕ}
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial σ (ZMod p)) (x : σ → ZMod p) :
    ‖polynomialCharacterWeight ψ G x‖ ≤ 1 :=
  DirichletCharacter.norm_le_one ψ (MvPolynomial.eval x G)

/-- All three properties in `eq:weightproperties`, for the actual finite-field
polynomial character weight. The manuscript specializes to `σ = Fin 4` and
`n ≥ 2`; positive degree suffices here. -/
theorem polynomialCharacterWeight_properties {σ : Type*} {p n : ℕ} [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) {G : MvPolynomial σ (ZMod p)}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (hψ : ψ ^ n = 1) :
    polynomialCharacterWeight ψ G (0 : σ → ZMod p) = 0 ∧
      (∀ x, ‖polynomialCharacterWeight ψ G x‖ ≤ 1) ∧
      (∀ (t : ZMod p), t ≠ 0 → ∀ x,
        polynomialCharacterWeight ψ G (t • x) = polynomialCharacterWeight ψ G x) := by
  refine ⟨polynomialCharacterWeight_zero ψ hG hn.ne', ?_, ?_⟩
  · exact polynomialCharacterWeight_norm_le_one ψ G
  · intro t ht x
    exact polynomialCharacterWeight_smul ψ hG hψ ht x

end QuaternaryQuadraticForms
