import QuaternaryQuadraticForms.Trusted.Katz

/-!
# The manuscript's quadric character-sum estimate

The good-prime matrix hypotheses supply the actual geometric smoothness and
irreducibility needed by the registered general spectral input. The
transverse polynomial is proved nonzero. The quadric Chern coefficient and
the final norm estimate are then deduced internally.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Lemma 2.7 over the prime field, with all geometric hypotheses supplied
by the actual matrix and the manuscript's rank-two condition. -/
theorem katz_quadric_bound_prime_field (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :
    ‖projectiveTrace A ψ G‖ ≤ (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) := by
  have h2 := primeField_two_ne_zero p hp
  obtain ⟨r, eigenvalues, hr, htrace, hnorm⟩ :=
    Trusted.katz_surface_spectral_data p (matrixQuadraticPolynomial A) G 2 n
      (by decide) (by omega) (matrixQuadraticPolynomial_homogeneous A)
      (matrixQuadraticPolynomial_ne_zero A hA hdet h2)
      hG (quadric_transverse_polynomial_ne_zero p A G htrans)
      (matrixQuadraticPolynomial_irreducible_map _ A hA hdet h2)
      (matrixQuadratic_projective_smooth_map _ A hA hdet h2)
      htrans ψ hψ horder quadricChernPolynomial quadricChernPolynomial_relation
  have hrInt : (r : ℤ) = 2 * (n : ℤ) ^ 2 - 4 * (n : ℤ) + 4 :=
    hr.trans (quadric_surfaceSectionEulerCoefficient n)
  have hrReal : (r : ℝ) = 2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4 := by
    exact_mod_cast hrInt
  rw [projectiveHypersurfaceTrace_matrix] at htrace
  rw [htrace]
  calc
    ‖∑ i, eigenvalues i‖ ≤ (r : ℝ) * (p : ℝ) :=
      norm_sum_le_card_mul eigenvalues (p : ℝ) (fun i => (hnorm i).le)
    _ = (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) := by rw [hrReal]

/-- Complete Lemma 2.7 with the original integral matrix and the literal
good-prime condition. The sum is the manuscript's actual projective trace. -/
theorem katz_quadric_bound (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :
    ‖projectiveTrace (reduceQuadraticMatrix p A) ψ G‖ ≤
      (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) :=
  katz_quadric_bound_prime_field p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) ψ hψ hG hn horder htrans

end QuaternaryQuadraticForms
