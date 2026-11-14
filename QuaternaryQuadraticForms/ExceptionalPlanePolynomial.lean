import QuaternaryQuadraticForms.ExceptionalPlaneDegree
import QuaternaryQuadraticForms.PlaneResultantSpecialization
import QuaternaryQuadraticForms.BertiniPlane
import QuaternaryQuadraticForms.BadReductionResultants
import QuaternaryQuadraticForms.QuadricSmooth

/-!
# The exceptional-plane polynomial

The general Bertini input supplies a transverse plane over the algebraic
closure. The fixed integral resultant family then has a nonzero specialized
member over the base field. Multiplication by the actual dual quadratic
polynomial gives the polynomial in Lemma 4.1(ii), with its degree bound
chosen before the form or the prime. No base-field transverse plane is
assumed or required.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The exceptional polynomial over any field of odd characteristic with
nonsingular quadratic reduction. The degree bound is chosen for the fixed
integral matrix and degree before the coefficient field and form. -/
theorem exceptional_plane_polynomial_over_fields
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
        (A.map (Int.castRingHom K)).det ≠ 0 →
        ∀ (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
          ProjectiveIntersectionTransverseRank
            ((matrixQuadraticPolynomial (A.map (Int.castRingHom K))).map
              (algebraMap K (AlgebraicClosure K)))
            (G.map (algebraMap K (AlgebraicClosure K))) →
          ∃ D : MvPolynomial (Fin 4) K,
            D ≠ 0 ∧ D.totalDegree ≤ E ∧ MvPolynomial.eval 0 D = 0 ∧
            ∀ u : Fin 4 → K, MvPolynomial.eval u D ≠ 0 →
              dotProduct u ((A.map (Int.castRingHom K)).adjugate.mulVec u) ≠ 0 ∧
              PlaneTransverseRank
                ((matrixQuadraticPolynomial (A.map (Int.castRingHom K))).map
                  (algebraMap K (AlgebraicClosure K)))
                (G.map (algebraMap K (AlgebraicClosure K)))
                ((algebraMap K (AlgebraicClosure K)) ∘ u) := by
  classical
  obtain ⟨s, R, hR⟩ := exceptionalPlane_resultants_over_fields A n hn
  let E := 2 + Finset.univ.sup (fun j : Fin s => (R j).totalDegree)
  refine ⟨E, by dsimp [E]; omega, ?_⟩
  intro K _ h2 hdet G hG htrans
  let f := algebraMap K (AlgebraicClosure K)
  let AK := A.map (Int.castRingHom K)
  obtain ⟨u₀, _, hu₀⟩ := exists_transverse_plane_of_smooth_intersection
    (AlgebraicClosure K) ((matrixQuadraticPolynomial AK).map f) (G.map f)
    ((matrixQuadraticPolynomial_homogeneous AK).map f) (hG.map f) hn htrans
  have hmatrix :
      matrixQuadraticPolynomial (A.map (Int.castRingHom (AlgebraicClosure K))) =
        (matrixQuadraticPolynomial AK).map f := by
    rw [matrixQuadraticPolynomial_map_ring]
    congr 1
  have hRgeom := hR (AlgebraicClosure K) (G.map f) (hG.map f) u₀
  rw [hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed,
    exists_planeReductionSystem_zero_iff, hmatrix] at hRgeom
  obtain ⟨j, hj⟩ : ∃ j : Fin s,
      MvPolynomial.eval u₀ (specializePlaneResultant (G.map f) (R j)) ≠ 0 := by
    by_contra! hz
    apply (hRgeom.mpr ?_) hu₀
    simpa only [eval_specializePlaneResultant] using hz
  let S := specializePlaneResultant G (R j)
  have hS : S ≠ 0 := by
    intro hz
    apply hj
    rw [← specializePlaneResultant_map f]
    change MvPolynomial.eval u₀ (S.map f) = 0
    rw [hz, map_zero, map_zero]
  let Fdual := matrixQuadraticPolynomial AK.adjugate
  have hAK : AK.transpose = AK :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M.map (Int.castRingHom K)) hA
  have hdual : Fdual ≠ 0 := by
    apply matrixQuadraticPolynomial_ne_zero
    · rw [Matrix.adjugate_transpose, hAK]
    · rw [Matrix.det_adjugate]
      exact pow_ne_zero _ hdet
    · exact h2
  refine ⟨Fdual * S, mul_ne_zero hdual hS, ?_, ?_, ?_⟩
  · calc
      (Fdual * S).totalDegree ≤ Fdual.totalDegree + S.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 + (R j).totalDegree := Nat.add_le_add
        (matrixQuadraticPolynomial_totalDegree_le AK.adjugate)
        (totalDegree_specializePlaneResultant_le G (R j))
      _ ≤ E := Nat.add_le_add_left
        (Finset.le_sup (f := fun j : Fin s => (R j).totalDegree)
          (Finset.mem_univ j)) 2
  · rw [map_mul]
    have hz : MvPolynomial.eval (0 : Fin 4 → K) Fdual = 0 := by
      change MvPolynomial.eval 0 (matrixQuadraticPolynomial AK.adjugate) = 0
      rw [eval_matrixQuadraticPolynomial]
      simp
    rw [hz, zero_mul]
  · intro u hu
    have hparts : MvPolynomial.eval u Fdual ≠ 0 ∧ MvPolynomial.eval u S ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [map_mul] using hu)
    refine ⟨?_, ?_⟩
    · simpa only [Fdual, eval_matrixQuadraticPolynomial] using hparts.1
    · by_contra hbad
      have hsystem := hR K G hG u
      rw [hasNonzeroGeometricZero_planeReductionSystem_iff] at hsystem
      apply hparts.2
      exact (eval_specializePlaneResultant G u (R j)).trans (hsystem.mp hbad j)

/-- Lemma 4.1(ii), under the literal characteristic-zero smoothness and
good-modulus hypotheses of the manuscript. Finiteness in the definition
of `N_G` is supplied by the already proved part (i). -/
theorem exceptional_plane_polynomial
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n)
        (hsmooth : SmoothCharacteristicZero A G)
        (p : ℕ) [Fact p.Prime],
        ¬ p ∣ polynomialBadPrimeModulus A G
          (badReductionPrimes_finite_of_smooth A hn G hG hsmooth) →
        ∃ D : MvPolynomial (Fin 4) (ZMod p),
          D ≠ 0 ∧ D.totalDegree ≤ E ∧ MvPolynomial.eval 0 D = 0 ∧
          ∀ u : Fin 4 → ZMod p, MvPolynomial.eval u D ≠ 0 →
            dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0 ∧
            PlaneTransverseRank
              ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
                (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
              ((G.map (Int.castRingHom (ZMod p))).map
                (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
              ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u) := by
  obtain ⟨E, hE, hpoly⟩ := exceptional_plane_polynomial_over_fields A hA n hn
  refine ⟨E, hE, ?_⟩
  intro G hG hsmooth p _ hp
  have hfinite := badReductionPrimes_finite_of_smooth A hn G hG hsmooth
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  exact hpoly (ZMod p) (primeField_two_ne_zero p (goodPrime_ne_two p A hpF))
    (goodPrime_reduced_det_ne_zero p A hpF) (G.map (Int.castRingHom (ZMod p)))
    (hG.map (Int.castRingHom (ZMod p))) hgood

end QuaternaryQuadraticForms
