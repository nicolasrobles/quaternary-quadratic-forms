import QuaternaryQuadraticForms.Trusted.Elimination

/-!
# Polynomial parameters in the resultant system

The published input is expressed in independent generic coefficients.
Here the coefficients are replaced by actual integer polynomials in a
parameter vector. Reconstruction of the forms and composition of evaluation
prove that the same resulting family works over every coefficient field.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The coefficient polynomials of a homogeneous family reconstruct its
specialization at every parameter point. -/
theorem homogeneousSystem_parameter_coefficients
    {ι σ : Type} {N : ℕ} (d : ι → ℕ)
    (P : ι → MvPolynomial (Fin N) (MvPolynomial σ ℤ))
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    {K : Type} [Field K] (a : σ → K) :
    homogeneousSystem N d
      (fun z => MvPolynomial.eval₂ (Int.castRingHom K) a ((P z.1).coeff z.2.val)) =
    fun i => (P i).map (MvPolynomial.eval₂Hom (Int.castRingHom K) a) := by
  funext i
  have h := congrArg
    (MvPolynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) a))
    (homogeneousForm_coefficients (P i) (hP i))
  simpa only [homogeneousSystem, homogeneousForm_map, MvPolynomial.coe_eval₂Hom] using h

/-- Substituting the actual coefficient polynomials into Lang's fixed
generic resultant family gives a fixed integer family in the parameters.
The output family precedes the field and the parameter assignment. -/
theorem homogeneous_parameter_resultants
    (N : ℕ) (hN : 0 < N) (ι : Type) [Fintype ι] [Nonempty ι]
    (σ : Type) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (P : ι → MvPolynomial (Fin N) (MvPolynomial σ ℤ))
    (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial σ ℤ),
      ∀ (K : Type) [Field K] (a : σ → K),
        HasNonzeroGeometricZero
          (fun i => (P i).map (MvPolynomial.eval₂Hom (Int.castRingHom K) a)) ↔
          ∀ j, MvPolynomial.eval₂ (Int.castRingHom K) a (R j) = 0 := by
  obtain ⟨s, U, hU⟩ := Trusted.lang_homogeneous_resultants N hN ι d hd
  let c : HomogeneousCoefficient N d → MvPolynomial σ ℤ :=
    fun z => (P z.1).coeff z.2.val
  refine ⟨s, fun j => MvPolynomial.eval₂ MvPolynomial.C c (U j), ?_⟩
  intro K _ a
  have h := hU K (fun z => MvPolynomial.eval₂ (Int.castRingHom K) a (c z))
  rw [show homogeneousSystem N d
      (fun z => MvPolynomial.eval₂ (Int.castRingHom K) a (c z)) =
      (fun i => (P i).map (MvPolynomial.eval₂Hom (Int.castRingHom K) a)) from
    homogeneousSystem_parameter_coefficients d P hP a] at h
  simpa only [MvPolynomial.eval₂_assoc] using h

end QuaternaryQuadraticForms
