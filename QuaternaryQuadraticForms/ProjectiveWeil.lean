import QuaternaryQuadraticForms.ProjectiveLine
import QuaternaryQuadraticForms.BinaryForms
import QuaternaryQuadraticForms.BinaryFormRoots
import QuaternaryQuadraticForms.PolynomialWeights
import QuaternaryQuadraticForms.WeilBound

/-!
# Character sums on the projective line

The sum is over mathlib's actual projective quotient. Homogeneity and the
character-order condition prove representative independence. The affine
chart is the literal polynomial `g(X,1)`, and the separate point at infinity
contributes at most one to the norm.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

local instance (p : ℕ) [Fact p.Prime] :
    Fintype (ℙ (ZMod p) (Fin 2 → ZMod p)) := Fintype.ofFinite _

/-- The actual projective-line sum appearing in Corollary 2.6. -/
def projectiveLineCharacterSum (p : ℕ) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (g : MvPolynomial (Fin 2) (ZMod p)) : ℂ :=
  ∑ P : ℙ (ZMod p) (Fin 2 → ZMod p), polynomialCharacterWeight ψ g P.rep

/-- The projective sum splits into the point at infinity and its affine chart. -/
theorem projectiveLineCharacterSum_chart (p : ℕ) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) {g : MvPolynomial (Fin 2) (ZMod p)} {n : ℕ}
    (hg : g.IsHomogeneous n) (horder : ψ ^ n = 1) :
    projectiveLineCharacterSum p ψ g =
      ψ (MvPolynomial.eval ![1, 0] g) + ∑ z : ZMod p, ψ ((binaryDehom g).eval z) := by
  unfold projectiveLineCharacterSum
  rw [sum_projectiveLine _ (polynomialCharacterWeight_units_smul ψ hg horder)]
  simp only [polynomialCharacterWeight, binaryVector_eq_vec, binaryDehom_eval]

/-- The norm estimate once the affine polynomial's geometric roots have been
checked. The subsequent source theorem supplies these hypotheses from the
literal projective geometric zero set. -/
theorem projectiveLineCharacterSum_bound_of_affine_roots
    (p : ℕ) [Fact p.Prime] (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {g : MvPolynomial (Fin 2) (ZMod p)} {n : ℕ}
    (hg : g.IsHomogeneous n) (horder : ψ ^ n = 1)
    (hdegree : 0 < (binaryDehom g).natDegree)
    (hroots : Fintype.card ((binaryDehom g).rootSet (AlgebraicClosure (ZMod p))) =
      (binaryDehom g).natDegree) :
    ‖projectiveLineCharacterSum p ψ g‖ ≤ ((n : ℝ) - 1) * Real.sqrt p + 1 := by
  rw [projectiveLineCharacterSum_chart p ψ hg horder]
  calc
    _ ≤ ‖ψ (MvPolynomial.eval ![1, 0] g)‖ +
          ‖∑ z : ZMod p, ψ ((binaryDehom g).eval z)‖ := norm_add_le _ _
    _ ≤ 1 + (((binaryDehom g).natDegree : ℝ) - 1) * Real.sqrt p :=
      add_le_add (DirichletCharacter.norm_le_one ψ _)
        (weil_bound p ψ hψ (binaryDehom g) _ hdegree rfl hroots)
    _ ≤ 1 + ((n : ℝ) - 1) * Real.sqrt p := by
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (Nat.cast_le.mpr (binaryDehom_natDegree_le hg)) 1)
        (Real.sqrt_nonneg _)
    _ = ((n : ℝ) - 1) * Real.sqrt p + 1 := add_comm _ _

/-- Corollary 2.6, under the literal manuscript hypotheses. The geometric
root condition counts actual projective zeros over an algebraic closure. -/
theorem projective_weil_bound (p : ℕ) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {g : MvPolynomial (Fin 2) (ZMod p)} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) (hn : 2 ≤ n)
    (horder : ψ ^ n = 1)
    (hroots : Nat.card (geometricBinaryProjectiveZeros g) = n) :
    ‖projectiveLineCharacterSum p ψ g‖ ≤ ((n : ℝ) - 1) * Real.sqrt p + 1 := by
  have hdata := binaryDehom_geometric_data hg hg0 hn hroots
  exact projectiveLineCharacterSum_bound_of_affine_roots p ψ hψ hg horder
    hdata.1 hdata.2.2

end QuaternaryQuadraticForms
