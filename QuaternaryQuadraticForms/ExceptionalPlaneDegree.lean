import QuaternaryQuadraticForms.ExceptionalPlaneResultants
import QuaternaryQuadraticForms.ParameterSpecialization

/-!
# Uniform degree of the exceptional-plane resultant family

The integral parameter polynomials are fixed before choosing the coefficient
field and the form. Partial specialization cannot increase total degree,
so one bound works for every form and in every characteristic.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Specializing the coefficients of the form cannot increase the degree
of a resultant polynomial in the remaining plane-normal variables. -/
theorem totalDegree_specializePlaneResultant_le
    {K : Type*} [Field K] {n : ℕ} (G : MvPolynomial (Fin 4) K)
    (P : MvPolynomial (ExceptionalPlaneParameter n) ℤ) :
    (specializePlaneResultant G P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_eval₂_le_of_degree_one
  intro i
  rcases i with m | j
  · simp only [Sum.elim_inl, MvPolynomial.totalDegree_C, zero_le]
  · simp only [Sum.elim_inr, MvPolynomial.totalDegree_X, le_refl]

/-- The degree bound and integral family are chosen before the coefficient
field and the degree-`n` form. Their simultaneous zeros detect the literal
geometric failure of rank-three transversality. This does not yet assert
that one specialized polynomial is nonzero; that needs a transverse plane. -/
theorem exceptionalPlane_bounded_resultant_family
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (E s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      1 ≤ E ∧
      ∀ (K : Type) [Field K] (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        (∀ j, (specializePlaneResultant G (R j)).totalDegree ≤ E) ∧
        ∀ u : Fin 4 → K,
          (¬ PlaneTransverseRank
            ((matrixQuadraticPolynomial (A.map (Int.castRingHom K))).map
              (algebraMap K (AlgebraicClosure K)))
            (G.map (algebraMap K (AlgebraicClosure K)))
            ((algebraMap K (AlgebraicClosure K)) ∘ u) ↔
            ∀ j, MvPolynomial.eval u (specializePlaneResultant G (R j)) = 0) := by
  classical
  obtain ⟨s, R, hR⟩ := exceptionalPlane_specialized_resultant_family A n hn
  let E := max 1 (Finset.univ.sup (fun j : Fin s => (R j).totalDegree))
  refine ⟨E, s, R, le_max_left _ _, ?_⟩
  intro K _ G hG
  refine ⟨?_, hR K G hG⟩
  intro j
  exact (totalDegree_specializePlaneResultant_le G (R j)).trans
    ((Finset.le_sup (f := fun j : Fin s => (R j).totalDegree)
      (Finset.mem_univ j)).trans (le_max_right _ _))

end QuaternaryQuadraticForms
