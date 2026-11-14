import QuaternaryQuadraticForms.PlaneReductionSystem
import QuaternaryQuadraticForms.GenericQuadricFamily
import QuaternaryQuadraticForms.EliminationFamily

/-!
# Universal resultants for the nontransverse-plane equations

The coefficient parameters of the degree-`n` form and the four coordinates
of the plane normal are indeterminates in one fixed integral polynomial
ring. Homogeneous elimination produces a finite family in those parameters
before a field, form or plane is chosen. Specialization gives the actual
three-row rank-failure system, including at geometric points.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Parameters for a form of degree `n` and its plane normal. -/
abbrev ExceptionalPlaneParameter (n : ℕ) := HomogeneousMonomial 4 n ⊕ Fin 4

/-- The fixed integral quadratic matrix in the joint parameter ring. -/
def genericPlaneQuadricMatrix (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (ExceptionalPlaneParameter n) ℤ) :=
  fun i j => MvPolynomial.C (A i j)

/-- The form coefficients are the first group of joint parameters. -/
def genericPlaneDegreeForm (n : ℕ) :
    MvPolynomial (Fin 4) (MvPolynomial (ExceptionalPlaneParameter n) ℤ) :=
  homogeneousForm (fun m => MvPolynomial.X (Sum.inl m))

/-- The plane normal is the second group of joint parameters. -/
def genericPlaneNormal (n : ℕ) (i : Fin 4) :
    MvPolynomial (ExceptionalPlaneParameter n) ℤ := MvPolynomial.X (Sum.inr i)

/-- The literal second system, before specialization of any parameters. -/
def genericPlaneReductionSystem (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) :
    PlaneReductionIndex →
      MvPolynomial (Fin 4) (MvPolynomial (ExceptionalPlaneParameter n) ℤ) :=
  planeReductionSystem (genericPlaneQuadricMatrix A n)
    (genericPlaneDegreeForm n) (genericPlaneNormal n)

/-- The form with joint indeterminate parameters is homogeneous of degree `n`. -/
theorem genericPlaneDegreeForm_homogeneous (n : ℕ) :
    (genericPlaneDegreeForm n).IsHomogeneous n :=
  homogeneousForm_isHomogeneous _

/-- Every equation in the second universal system has its assigned degree. -/
theorem genericPlaneReductionSystem_homogeneous
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ} (hn : 2 ≤ n)
    (k : PlaneReductionIndex) :
    (genericPlaneReductionSystem A n k).IsHomogeneous (planeReductionSystemDegree n k) :=
  planeReductionSystem_homogeneous _ _ hn (genericPlaneDegreeForm_homogeneous n) _ k

/-- Evaluation of the joint parameters preserves the fixed matrix. -/
theorem genericPlaneQuadricMatrix_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ)
    (c : HomogeneousMonomial 4 n → R) (u : Fin 4 → R) :
    (genericPlaneQuadricMatrix A n).map (MvPolynomial.eval₂Hom f (Sum.elim c u)) =
      A.map f := by
  ext i j
  exact MvPolynomial.eval₂Hom_C f (Sum.elim c u) (A i j)

/-- The generic form specializes to the form with the chosen literal coefficients. -/
theorem genericPlaneDegreeForm_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (n : ℕ) (c : HomogeneousMonomial 4 n → R) (u : Fin 4 → R) :
    (genericPlaneDegreeForm n).map (MvPolynomial.eval₂Hom f (Sum.elim c u)) =
      homogeneousForm c := by
  rw [genericPlaneDegreeForm, homogeneousForm_map]
  simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl]

/-- The generic normal specializes to the chosen four coordinates. -/
theorem genericPlaneNormal_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (n : ℕ) (c : HomogeneousMonomial 4 n → R) (u : Fin 4 → R) :
    (MvPolynomial.eval₂Hom f (Sum.elim c u)) ∘ genericPlaneNormal n = u := by
  funext i
  exact MvPolynomial.eval₂Hom_X' f (Sum.elim c u) (Sum.inr i)

/-- Coefficient specialization produces the entire literal plane system. -/
theorem genericPlaneReductionSystem_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ)
    (c : HomogeneousMonomial 4 n → R) (u : Fin 4 → R) (k : PlaneReductionIndex) :
    (genericPlaneReductionSystem A n k).map (MvPolynomial.eval₂Hom f (Sum.elim c u)) =
      planeReductionSystem (A.map f) (homogeneousForm c) u k := by
  rw [genericPlaneReductionSystem, planeReductionSystem_map,
    genericPlaneQuadricMatrix_map_eval₂Hom, genericPlaneDegreeForm_map_eval₂Hom,
    genericPlaneNormal_eval₂Hom]

/-- Inserting the actual coefficients of `G` gives its actual second system. -/
theorem genericPlaneReductionSystem_specialize {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (G : MvPolynomial (Fin 4) R) (hG : G.IsHomogeneous n)
    (u : Fin 4 → R) (k : PlaneReductionIndex) :
    (genericPlaneReductionSystem A n k).map
      (MvPolynomial.eval₂Hom (Int.castRingHom R)
        (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u)) =
      planeReductionSystem (A.map (Int.castRingHom R)) G u k := by
  rw [genericPlaneReductionSystem_map_eval₂Hom, homogeneousForm_coefficients G hG]

/-- A fixed integral family in `(g,u)` detects geometric nontransversality
for every field and every homogeneous form of degree `n` over that field. -/
theorem exceptionalPlane_resultants_over_fields
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      ∀ (K : Type) [Field K] (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        ∀ u : Fin 4 → K,
          (HasNonzeroGeometricZero
            (planeReductionSystem (A.map (Int.castRingHom K)) G u) ↔
            ∀ j, MvPolynomial.eval₂ (Int.castRingHom K)
              (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u)
              (R j) = 0) := by
  obtain ⟨s, R, hR⟩ := homogeneous_parameter_resultants 4 (by decide)
    PlaneReductionIndex (ExceptionalPlaneParameter n) (planeReductionSystemDegree n)
    (planeReductionSystemDegree_pos hn) (genericPlaneReductionSystem A n)
    (genericPlaneReductionSystem_homogeneous A hn)
  refine ⟨s, R, ?_⟩
  intro K _ G hG u
  have h := hR K (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u)
  have hsystem :
      (fun i => (genericPlaneReductionSystem A n i).map
        (MvPolynomial.eval₂Hom (Int.castRingHom K)
          (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u))) =
      planeReductionSystem (A.map (Int.castRingHom K)) G u := by
    funext i
    exact genericPlaneReductionSystem_specialize A G hG u i
  rwa [hsystem] at h

/-- The same fixed family detects the manuscript's actual geometric rank failure. -/
theorem exceptionalPlane_resultant_family
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      ∀ (K : Type) [Field K] (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        ∀ u : Fin 4 → K,
          (¬ PlaneTransverseRank
            ((matrixQuadraticPolynomial (A.map (Int.castRingHom K))).map
              (algebraMap K (AlgebraicClosure K)))
            (G.map (algebraMap K (AlgebraicClosure K)))
            ((algebraMap K (AlgebraicClosure K)) ∘ u) ↔
            ∀ j, MvPolynomial.eval₂ (Int.castRingHom K)
              (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u)
              (R j) = 0) := by
  obtain ⟨s, R, hR⟩ := exceptionalPlane_resultants_over_fields A n hn
  refine ⟨s, R, ?_⟩
  intro K _ G hG u
  rw [← hasNonzeroGeometricZero_planeReductionSystem_iff]
  exact hR K G hG u

/-- Specialize only the coefficients of `G`, leaving the four plane-normal
coordinates as polynomial variables over the chosen coefficient ring. -/
def specializePlaneResultant {R : Type*} [CommRing R] {n : ℕ}
    (G : MvPolynomial (Fin 4) R)
    (P : MvPolynomial (ExceptionalPlaneParameter n) ℤ) : MvPolynomial (Fin 4) R :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp (Int.castRingHom R))
    (Sum.elim (fun m : HomogeneousMonomial 4 n => MvPolynomial.C (G.coeff m.val))
      MvPolynomial.X) P

/-- Evaluation after partial specialization is the joint parameter evaluation. -/
theorem eval_specializePlaneResultant {R : Type*} [CommRing R] {n : ℕ}
    (G : MvPolynomial (Fin 4) R) (u : Fin 4 → R)
    (P : MvPolynomial (ExceptionalPlaneParameter n) ℤ) :
    MvPolynomial.eval u (specializePlaneResultant G P) =
      MvPolynomial.eval₂ (Int.castRingHom R)
        (Sum.elim (fun m : HomogeneousMonomial 4 n => G.coeff m.val) u) P := by
  rw [specializePlaneResultant, MvPolynomial.eval_eval₂]
  congr 1
  · exact RingHom.ext_int _ _
  · funext z
    rcases z with m | i
    · exact MvPolynomial.eval_C _
    · exact MvPolynomial.eval_X _

/-- One fixed family can equally be stated using polynomials in the plane
normal after specialization of the coefficients of `G`. -/
theorem exceptionalPlane_specialized_resultant_family
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (ExceptionalPlaneParameter n) ℤ),
      ∀ (K : Type) [Field K] (G : MvPolynomial (Fin 4) K), G.IsHomogeneous n →
        ∀ u : Fin 4 → K,
          (¬ PlaneTransverseRank
            ((matrixQuadraticPolynomial (A.map (Int.castRingHom K))).map
              (algebraMap K (AlgebraicClosure K)))
            (G.map (algebraMap K (AlgebraicClosure K)))
            ((algebraMap K (AlgebraicClosure K)) ∘ u) ↔
            ∀ j, MvPolynomial.eval u (specializePlaneResultant G (R j)) = 0) := by
  obtain ⟨s, R, hR⟩ := exceptionalPlane_resultant_family A n hn
  refine ⟨s, R, ?_⟩
  intro K _ G hG u
  simpa only [eval_specializePlaneResultant] using hR K G hG u

end QuaternaryQuadraticForms
