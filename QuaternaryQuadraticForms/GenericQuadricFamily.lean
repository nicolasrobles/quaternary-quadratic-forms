import QuaternaryQuadraticForms.HomogeneousForms
import QuaternaryQuadraticForms.BadReductionSystem

/-!
# The fixed quadric and a form with indeterminate coefficients

The parameters are the literal coefficients of a degree-`n` homogeneous
form in four variables. The quadratic matrix is fixed over the integers.
Specialization of this family gives exactly the original two equations
and their gradient minors, including after reduction of the coefficients.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The fixed integral quadratic matrix over the parameter ring. -/
def genericQuadricMatrix {n : ℕ} (A : Matrix (Fin 4) (Fin 4) ℤ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (HomogeneousMonomial 4 n) ℤ) :=
  fun i j => MvPolynomial.C (A i j)

/-- The degree-`n` homogeneous form with one indeterminate coefficient
for every monomial of that degree. -/
def genericDegreeForm (n : ℕ) :
    MvPolynomial (Fin 4) (MvPolynomial (HomogeneousMonomial 4 n) ℤ) :=
  homogeneousForm (fun m => MvPolynomial.X m)

/-- The two equations and their gradient minors over the parameter ring. -/
def genericBadReductionSystem (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) :
    BadReductionIndex →
      MvPolynomial (Fin 4) (MvPolynomial (HomogeneousMonomial 4 n) ℤ) :=
  badReductionSystem (genericQuadricMatrix A) (genericDegreeForm n)

/-- Homogeneity of the generic form is independent of its coefficients. -/
theorem genericDegreeForm_homogeneous (n : ℕ) :
    (genericDegreeForm n).IsHomogeneous n :=
  homogeneousForm_isHomogeneous _

/-- Every equation in the generic system has its prescribed homogeneous
degree in the four geometric variables. -/
theorem genericBadReductionSystem_homogeneous
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ} (hn : 2 ≤ n)
    (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).IsHomogeneous (badReductionSystemDegree n k) :=
  badReductionSystem_homogeneous _ _ hn (genericDegreeForm_homogeneous n) k

/-- Specializing the parameters leaves the fixed quadratic matrix equal
to its image under the chosen homomorphism from the integers. -/
theorem genericQuadricMatrix_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (w : HomogeneousMonomial 4 n → R) :
    (genericQuadricMatrix A).map (MvPolynomial.eval₂Hom f w) = A.map f := by
  ext i j
  exact MvPolynomial.eval₂Hom_C f w (A i j)

/-- The generic form specializes to the form with exactly the chosen
coefficient vector, over any commutative ring. -/
theorem genericDegreeForm_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (n : ℕ) (w : HomogeneousMonomial 4 n → R) :
    (genericDegreeForm n).map (MvPolynomial.eval₂Hom f w) = homogeneousForm w := by
  rw [genericDegreeForm, homogeneousForm_map]
  simp only [MvPolynomial.eval₂Hom_X']

/-- Specialization commutes with construction of the full system. -/
theorem genericBadReductionSystem_map_eval₂Hom {R : Type*} [CommRing R]
    (f : ℤ →+* R) (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ)
    (w : HomogeneousMonomial 4 n → R) (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).map (MvPolynomial.eval₂Hom f w) =
      badReductionSystem (A.map f) (homogeneousForm w) k := by
  rw [genericBadReductionSystem, badReductionSystem_map,
    genericQuadricMatrix_map_eval₂Hom, genericDegreeForm_map_eval₂Hom]

/-- Inserting the actual coefficients of a homogeneous polynomial gives
its literal bad-reduction system, with the fixed integral quadratic matrix. -/
theorem genericBadReductionSystem_specialize {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (G : MvPolynomial (Fin 4) R) (hG : G.IsHomogeneous n) (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).map
        (MvPolynomial.eval₂Hom (Int.castRingHom R)
          (fun m : HomogeneousMonomial 4 n => G.coeff m.val)) =
      badReductionSystem (A.map (Int.castRingHom R)) G k := by
  rw [genericBadReductionSystem_map_eval₂Hom, homogeneousForm_coefficients G hG]

/-- The integral specialization uses ordinary integer evaluation at the
literal coefficients of `G`. -/
theorem genericBadReductionSystem_specialize_integral
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n) (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).map
        (MvPolynomial.eval (fun m : HomogeneousMonomial 4 n => G.coeff m.val)) =
      badReductionSystem A G k := by
  change (genericBadReductionSystem A n k).map
      (MvPolynomial.eval₂Hom (RingHom.id ℤ)
        (fun m : HomogeneousMonomial 4 n => G.coeff m.val)) = _
  rw [genericBadReductionSystem_map_eval₂Hom, homogeneousForm_coefficients G hG]
  rfl

/-- After any map from the integers, the parameter vector is the image
of the original integer coefficient vector. This applies in particular
to prime fields and their algebraic closures. -/
theorem genericBadReductionSystem_specialize_map {R : Type*} [CommRing R]
    (f : ℤ →+* R) (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n) (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).map
        (MvPolynomial.eval₂Hom f
          (fun m : HomogeneousMonomial 4 n => f (G.coeff m.val))) =
      badReductionSystem (A.map f) (G.map f) k := by
  rw [genericBadReductionSystem_map_eval₂Hom, ← homogeneousForm_map,
    homogeneousForm_coefficients G hG]

/-- The integer-cast specialization of the same fixed integral family. -/
theorem genericBadReductionSystem_specialize_intCast {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ}
    (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n) (k : BadReductionIndex) :
    (genericBadReductionSystem A n k).map
        (MvPolynomial.eval₂Hom (Int.castRingHom R)
          (fun m : HomogeneousMonomial 4 n => ((G.coeff m.val : ℤ) : R))) =
      badReductionSystem (A.map (Int.castRingHom R)) (G.map (Int.castRingHom R)) k :=
  genericBadReductionSystem_specialize_map (Int.castRingHom R) A G hG k

end QuaternaryQuadraticForms
