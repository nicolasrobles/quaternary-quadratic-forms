import QuaternaryQuadraticForms.HomogeneousForms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Coefficient data for homogeneous elimination

The coefficient space contains every monomial of each assigned degree.
The common-zero predicate is projective: it requires a nonzero vector over
the algebraic closure of the coefficient field.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The coefficients of a finite family of homogeneous forms, with their
assigned degrees retained even when specialization gives the zero form. -/
abbrev HomogeneousCoefficient {ι : Type} (N : ℕ) (d : ι → ℕ) :=
  Σ i : ι, HomogeneousMonomial N (d i)

/-- A family of actual homogeneous polynomials at a coefficient point. -/
def homogeneousSystem {ι R : Type} [CommSemiring R] (N : ℕ) (d : ι → ℕ)
    (w : HomogeneousCoefficient N d → R) : ι → MvPolynomial (Fin N) R :=
  fun i => homogeneousForm (fun m => w ⟨i, m⟩)

/-- A common nonzero geometric zero of the given homogeneous equations. -/
def HasNonzeroGeometricZero {ι K : Type} [Field K] {N : ℕ}
    (P : ι → MvPolynomial (Fin N) K) : Prop :=
  ∃ x : Fin N → AlgebraicClosure K, x ≠ 0 ∧
    ∀ i, MvPolynomial.eval x
      ((P i).map (algebraMap K (AlgebraicClosure K))) = 0

end QuaternaryQuadraticForms
