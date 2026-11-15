import QuaternaryQuadraticForms.QuadricCountingDefinitions
import QuaternaryQuadraticForms.RationalQuadricNormalForm
import QuaternaryQuadraticForms.RationalQuadricLattice
import QuaternaryQuadraticForms.SplitQuadricCounting

/-!
# Lemma 2.3: integer zeros of a nonsplit rational quaternary form

The result counts the literal integer zeros in the actual Euclidean ball.
The rational hyperbolic normal form, the injective integral change of
variables, and the signed-divisor estimate are proved internally. No
literature premise or uniformity assumption on the radius is introduced.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The Euclidean finite count in Lemma 2.3. The constant is selected after
the rational form and positive epsilon, before every real radius at least one. -/
theorem rationalQuadric_euclidean_bound
    (S : Matrix (Fin 4) (Fin 4) ℚ) (hS : S.transpose = S)
    (hdet : S.det ≠ 0) (hns : ¬ IsSquare S.det)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ((integerQuadricZeros S U).card : ℝ) ≤ C * U ^ (2 + ε) := by
  classical
  by_cases hiso : ∃ e : Fin 4 → ℚ, e ≠ 0 ∧ dotProduct e (S.mulVec e) = 0
  · obtain ⟨T, a, b, c, hT, hnormal, haniso⟩ :=
      exists_rational_quadric_normal_form S hS hdet hns hiso
    obtain ⟨k, a', b', c', L, hk, hL, hbinary, hmap⟩ :=
      rationalQuadric_integer_model S T hT a b c hnormal haniso
    obtain ⟨D, hD, hcoord⟩ := integerMatrix_coordinate_bound L
    obtain ⟨C, hC, hcount⟩ := splitQuadric_box_bound k a' b' c' hk hbinary ε hε
    exact integerQuadricZeros_bound_of_lattice_model S ε L hL D hD hcoord
      (fun y => k * y 0 * y 1 + a' * y 2 ^ 2 + b' * y 2 * y 3 + c' * y 3 ^ 2 = 0)
      hmap C hC hcount
  · have haniso : ∀ x : Fin 4 → ℚ, dotProduct x (S.mulVec x) = 0 → x = 0 := by
      intro x hx
      by_contra hx0
      exact hiso ⟨x, hx0, hx⟩
    refine ⟨1, zero_lt_one, ?_⟩
    intro U hU
    calc
      ((integerQuadricZeros S U).card : ℝ) ≤ 1 := by
        exact_mod_cast integerQuadricZeros_card_le_one S haniso U
      _ ≤ 1 * U ^ (2 + ε) := by
        rw [one_mul]
        exact Real.one_le_rpow hU (by linarith)

/-- Complete source statement of Lemma 2.3: the literal set is finite and
its actual cardinality is at most C times U^(2+epsilon), uniformly in U>=1. -/
theorem source_quadric_count
    (S : Matrix (Fin 4) (Fin 4) ℚ) (hS : S.transpose = S)
    (hdet : S.det ≠ 0) (hns : ¬ IsSquare S.det)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      (sourceQuadricZeroSet S U).Finite ∧
      ((sourceQuadricZeroSet S U).ncard : ℝ) ≤ C * U ^ (2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := rationalQuadric_euclidean_bound S hS hdet hns ε hε
  refine ⟨C, hC, fun U hU => ⟨sourceQuadricZeroSet_finite S U, ?_⟩⟩
  rw [sourceQuadricZeroSet_ncard]
  exact hbound U hU

end QuaternaryQuadraticForms
