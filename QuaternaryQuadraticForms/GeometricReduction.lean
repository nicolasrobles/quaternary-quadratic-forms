import QuaternaryQuadraticForms.EliminationData
import QuaternaryQuadraticForms.BadReductionSystem

/-!
# Geometric zeros of the bad-reduction system

Homogeneous elimination extends the coefficient field to its algebraic
closure after specialization. The manuscript's rank condition uses the
same geometric points, with the integral equations mapped directly to
that algebraic closure. The lemmas below identify these two descriptions
without an additional geometric hypothesis.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The literal characteristic-zero smoothness hypothesis: the two
actual gradient rows have rank two at every nonzero common zero over the
algebraic closure of the rationals. -/
def SmoothCharacteristicZero (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) : Prop :=
  ProjectiveIntersectionTransverseRank
    ((matrixQuadraticPolynomial A).map (Int.castRingHom (AlgebraicClosure ℚ)))
    (G.map (Int.castRingHom (AlgebraicClosure ℚ)))

/-- For integral equations, specialization to a field and then extension
to its algebraic closure is the direct integer-cast evaluation. -/
theorem hasNonzeroGeometricZero_map_intCast_iff {ι K : Type} [Field K] {N : ℕ}
    (P : ι → MvPolynomial (Fin N) ℤ) :
    HasNonzeroGeometricZero (fun i => (P i).map (Int.castRingHom K)) ↔
      ∃ x : Fin N → AlgebraicClosure K, x ≠ 0 ∧
        ∀ i, MvPolynomial.eval₂ (Int.castRingHom (AlgebraicClosure K)) x (P i) = 0 := by
  have hmap : (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
      Int.castRingHom (AlgebraicClosure K) := RingHom.ext_int _ _
  simp only [HasNonzeroGeometricZero, MvPolynomial.eval_map,
    MvPolynomial.eval₂_map, hmap]

/-- The geometric zero predicate for the specialized integral system is
exactly failure of the two-gradient rank condition over the same algebraic
closure. -/
theorem hasNonzeroGeometricZero_badReductionSystem_iff {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ) :
    HasNonzeroGeometricZero
      (fun i => (badReductionSystem A G i).map (Int.castRingHom K)) ↔
      ¬ ProjectiveIntersectionTransverseRank
        ((matrixQuadraticPolynomial A).map (Int.castRingHom (AlgebraicClosure K)))
        (G.map (Int.castRingHom (AlgebraicClosure K))) := by
  rw [hasNonzeroGeometricZero_map_intCast_iff]
  exact exists_badReductionSystem_eval₂_zero_iff
    (Int.castRingHom (AlgebraicClosure K)) A G

/-- The characteristic-zero system has a nonzero geometric zero exactly
when the literal characteristic-zero smoothness hypothesis fails. -/
theorem hasNonzeroGeometricZero_badReductionSystem_rat_iff
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ) :
    HasNonzeroGeometricZero
      (fun i => (badReductionSystem A G i).map (Int.castRingHom ℚ)) ↔
      ¬ SmoothCharacteristicZero A G :=
  hasNonzeroGeometricZero_badReductionSystem_iff A G

/-- The prime-field system has a nonzero geometric zero exactly when
the manuscript's literal good-reduction condition fails at that prime. -/
theorem hasNonzeroGeometricZero_badReductionSystem_zmod_iff
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) :
    HasNonzeroGeometricZero
      (fun i => (badReductionSystem A G i).map (Int.castRingHom (ZMod p))) ↔
      ¬ GoodReductionAt p A G := by
  rw [hasNonzeroGeometricZero_map_intCast_iff]
  exact exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt p A G

end QuaternaryQuadraticForms
