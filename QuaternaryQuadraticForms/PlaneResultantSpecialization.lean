import QuaternaryQuadraticForms.ExceptionalPlaneResultants

/-!
# Geometric witnesses and specialization of the plane resultants

A field that is already algebraically closed has no additional common
zeros after passing to its algebraic closure. We also record that
specializing the form coefficients commutes with extension of the
coefficient field. These facts allow a geometric transverse-plane witness
to establish that one of the specialized resultant polynomials is nonzero.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Over an algebraically closed field the geometric common-zero
predicate is exactly the common-zero predicate in that field. -/
theorem hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed
    {ι K : Type} [Field K] [IsAlgClosed K] {N : ℕ}
    (P : ι → MvPolynomial (Fin N) K) :
    HasNonzeroGeometricZero P ↔
      ∃ x : Fin N → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (P i) = 0 := by
  classical
  let f := algebraMap K (AlgebraicClosure K)
  have hf : Function.Bijective f :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  constructor
  · rintro ⟨x, hx, hP⟩
    choose y hy using fun i => hf.surjective (x i)
    have hxy : f ∘ y = x := funext hy
    refine ⟨y, ?_, ?_⟩
    · intro hyzero
      apply hx
      rw [← hxy, hyzero]
      funext i
      exact map_zero f
    · intro i
      apply hf.injective
      rw [map_zero, MvPolynomial.eval₂_comp, ← MvPolynomial.eval_map, hxy]
      exact hP i
  · rintro ⟨x, hx, hP⟩
    refine ⟨f ∘ x, ?_, ?_⟩
    · intro hzero
      apply hx
      funext i
      apply hf.injective
      simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hzero i
    · intro i
      rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp, hP i, map_zero]

/-- Partial specialization of the form coefficients commutes with any
coefficient homomorphism, including passage to an algebraic closure. -/
theorem specializePlaneResultant_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (G : MvPolynomial (Fin 4) R)
    (P : MvPolynomial (ExceptionalPlaneParameter n) ℤ) :
    (specializePlaneResultant G P).map f =
      specializePlaneResultant (G.map f) P := by
  unfold specializePlaneResultant
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext z
    rcases z with m | i
    · simp only [Function.comp_apply, Sum.elim_inl, MvPolynomial.map_C,
        MvPolynomial.coeff_map]
    · simp only [Function.comp_apply, Sum.elim_inr, MvPolynomial.map_X]

/-- For an algebraically closed coefficient field, the fixed resultant
family detects the literal rank condition over that same field. -/
theorem exceptionalPlane_resultants_over_algClosed_fields
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      ∀ (K : Type) [Field K] [IsAlgClosed K]
        (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        ∀ u : Fin 4 → K,
          (¬ PlaneTransverseRank (matrixQuadraticPolynomial (A.map (Int.castRingHom K)))
            G u ↔ ∀ j, MvPolynomial.eval u (specializePlaneResultant G (R j)) = 0) := by
  obtain ⟨s, R, hR⟩ := exceptionalPlane_resultants_over_fields A n hn
  refine ⟨s, R, ?_⟩
  intro K _ _ G hG u
  have h := hR K G hG u
  rw [hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed,
    exists_planeReductionSystem_zero_iff] at h
  simpa only [eval_specializePlaneResultant] using h

/-- A transverse plane over an algebraically closed field forces a
nonzero evaluation of at least one member of the fixed resultant family. -/
theorem exceptionalPlane_resultants_nonzero_of_transverse_witness
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      ∀ (K : Type) [Field K] [IsAlgClosed K]
        (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        ∀ u : Fin 4 → K,
          PlaneTransverseRank (matrixQuadraticPolynomial (A.map (Int.castRingHom K))) G u →
          ∃ j, MvPolynomial.eval u (specializePlaneResultant G (R j)) ≠ 0 := by
  classical
  obtain ⟨s, R, hR⟩ := exceptionalPlane_resultants_over_algClosed_fields A n hn
  refine ⟨s, R, ?_⟩
  intro K _ _ G hG u hu
  by_contra! hz
  exact ((hR K G hG u).mpr hz) hu

end QuaternaryQuadraticForms
